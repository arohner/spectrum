(ns spectrum.ann
  (:require [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]
            [spectrum.java :as j]
            [spectrum.util :refer (print-once)])
  (:import (clojure.lang BigInt
                         Ratio)))

(s/def ::transformer (s/fspec :args (s/cat :spec ::c/spect :args-spec ::c/spect) :ret ::c/spect))

(s/fdef ann :args (s/cat :v var? :f ::transformer) :ret nil?)
(defn ann
  "Register a spec transformer. Takes a var or clojure.reflect.Method, and a transformer function

  transformer function: a function taking 2 args: the function's declared spect,
  and the Spect for the fn args at this callsite. Returns an updated
  spec. This is typically used to make :args or :ret more specific.

  The args must pass the original spect before transforming, so this can't
  be used to make the spec less specific.
  "
  [v f]
  (swap! data/invoke-transformers assoc v f)
  nil)

(ann #'instance? (fn [spect args-spect]
                   (let [c (c/first* args-spect)
                         x (c/second* args-spect)]
                     (if (and (c/known? c) (c/known? x))
                       (let [cs (c/spec->classes c)
                             xs (c/spec->classes x)
                             rets (for [c cs
                                        x xs]
                                    (c/conform (c/class-spec c) (c/class-spec x)))]
                         (if (every? c/conformy? rets)
                           (let [truth (set (map c/truthyness rets))
                                 ret (cond
                                       (contains? truth :ambiguous) (c/pred-spec #'boolean?)
                                       (> (count truth) 1) (c/pred-spec #'boolean?)
                                       (and (= 1 (count truth)) (= :truthy (first truth))) (c/value true)
                                       (and (= 1 (count truth)) (= :falsey (first truth))) (c/value false)
                                       :else (assert false "unreachable"))]
                             (assoc spect :ret ret))
                           (assoc spect :ret (c/value false))))
                       spect))))

(ann #'into (fn [spect args-spect]
              (let [to (c/first* args-spect)
                    from (c/second* args-spect)]
                (if (c/known? to)
                  (assoc spect :ret to)
                  spect))))

(s/fdef instance-or :args (s/cat :cls (s/coll-of class?)) :ret ::transformer)
(defn instance-or
  "spec-transformer for (or (instance? a) (instance? b)...) case. classes is a seq of classes."
  [classes]
  (fn [spect args-spect]
    (if (c/first-rest? args-spect)
      (let [spect* (c/or- (map c/class-spec classes))
            arg-spect (c/first* args-spect)
            conform-ret (c/conform spect* arg-spect)]
        (if (c/conformy? conform-ret)
          (let [truth (c/truthyness conform-ret)
                ret (condp = truth
                      :truthy (c/value true)
                      :falsey (c/value false)
                      (c/pred-spec #'boolean?))]
            (assoc spect :ret ret))
          (assoc spect :ret (c/value false))))
      (c/invalid {:message "args must support first-rest"}))))

(s/fdef instance-transformer :args (s/cat :c class?) :ret ::transformer)
(defn instance-transformer [cls]
  (instance-or [cls]))

(s/fdef protocol-transformer :args (s/cat :p any?) :ret ::transformer)
(defn protocol-transformer [protocol]
  (fn [spect args-spect]
    (let [arg (if (satisfies? c/FirstRest args-spect)
                (c/first* args-spect)
                args-spect)]
      (if arg
        (if (satisfies? protocol arg)
          (assoc spect :ret (c/value true))
          (assoc spect :ret (c/value false)))
        spect))))

(def pred->class
  {#'associative? clojure.lang.Associative
   #'boolean? Boolean
   #'bigdec? BigDecimal
   #'char? Character
   #'chunked-seq? clojure.lang.IChunkedSeq
   #'class? Class
   #'coll? clojure.lang.IPersistentCollection
   #'counted? clojure.lang.Counted
   #'decimal? BigDecimal
   #'delay? clojure.lang.Delay
   #'double? Double
   #'fn? clojure.lang.Fn
   #'future? java.util.concurrent.Future
   #'ifn? clojure.lang.IFn
   #'indexed? clojure.lang.Indexed
   #'inst? java.util.Date
   #'keyword? clojure.lang.Keyword
   #'list? clojure.lang.IPersistentList
   #'map-entry? java.util.Map$Entry
   #'map? clojure.lang.IPersistentMap
   #'number? Number
   #'ratio? clojure.lang.Ratio
   #'reader-conditional? clojure.lang.ReaderConditional
   #'reversible? clojure.lang.Reversible
   #'seq? clojure.lang.ISeq
   #'sequential? clojure.lang.Sequential
   #'set? clojure.lang.IPersistentSet
   #'sorted? clojure.lang.Sorted
   #'string? String
   #'symbol? clojure.lang.Symbol
   #'tagged-literal? clojure.lang.TaggedLiteral
   #'uri? java.net.URI
   #'uuid? java.util.UUID
   #'var? clojure.lang.Var
   #'vector? clojure.lang.IPersistentVector
   #'volatile? clojure.lang.Volatile
   })

(defn ann-instance?
  "Annotates var-predicate p as just a simple instanceof? check

   (ann-instance #'string? java.lang.String)
 "
  [v cls]
  (ann v (instance-or [cls]))
  (data/add-type-transformer v (c/class-spec cls)))

(doseq [[v cls] pred->class]
  (ann-instance? v cls))

(defn ann-protocol?
  "Annotates var-predicate p as just a simple satisfies? check

   (ann-protocol #'spect? Spect)
 "
  [v proto]
  (ann v (protocol-transformer proto)))


(defn ann-instance-or [v classes]
  (ann v (instance-or classes))
  (data/add-type-transformer v (c/or- (mapv c/class-spec classes))))

(ann-instance-or #'float? [Float Double])
(ann-instance-or #'int? [Long Integer Short Byte])
(ann-instance-or #'integer? [Long Integer Short Byte clojure.lang.BigInt BigInteger])
(ann-instance-or #'seqable? [clojure.lang.ISeq clojure.lang.Seqable Iterable CharSequence java.util.Map]) ;; TODO java array

(defn maybe-convert-value [x]
  (or (c/pred->value x) x))

(defn ann-nil-false [val]
  (fn [spect args-spect]
    (let [x (c/first* args-spect)
          truthyness (c/truthyness x)]
      (if (not= :ambiguous truthyness)
        (let [x (maybe-convert-value x)]
          (assoc spect :ret (cond
                              (= :truthy truthyness) (c/value false)
                              (c/value? x) (if (= val (:v x))
                                             (c/value true)
                                             (c/value false))
                              :else (:ret spect))))
        spect))))

(ann #'false? (ann-nil-false false))

(ann #'nil? (ann-nil-false nil))

(ann #'not (fn [spect args-spec]
             (let [x (c/first* args-spec)
                   x (maybe-convert-value x)]
               (if (c/value? x)
                 (assoc spect :ret (c/value (not (:v x))))
                 spect))))

(defn get-cat-vals
  "Given a Cat of Value, return the raw vals"
  [c]
  (mapv :v c))

(ann #'select-keys (fn [spect args-spect]
                     (let [m (c/first* args-spect)
                           select (c/second* args-spect)]
                       (if (and (c/keys-spec? m)
                                (c/value? select)
                                (coll? (:v select))
                                (every? (fn [v] (c/conform (c/pred-spec #'keyword?) v)) (:v select)))
                         (let [vals (get-cat-vals (:v select))]
                           (let [ret (c/keys-spec (select-keys (:req m) vals)
                                                  (select-keys (:req-un m) vals)
                                                  (select-keys (:opt m) vals)
                                                  (select-keys (:opt-un m) vals))]
                             (assoc spect :ret ret)))
                         spect))))

(s/fdef ann-method :args (s/cat :cls class? :method symbol? :args c/spect? :xfer fn?) :ret any?)

(defn ann-method
  "Ann a java method"
  [cls method-name args transformer]
  (let [method (flow/get-conforming-java-method cls method-name args)]
    (assert method (format "couldn't find method: %s %s %s" cls method-name (print-str args)))
    (ann method transformer)))

(s/fdef merge-keys :args (s/cat :m1 c/keys-spec? :m2 c/keys-spec?) :ret c/keys-spec?)
(defn merge-keys [m1 m2]
  (apply c/keys-spec (for [k [:req :req-un :opt :opt-un]]
                       (merge (get m1 k) (get m2 k)))))

(ann #'merge (fn [spect args-spect]
               (assert (c/cat-spec? args-spect))
               (if (every? c/keys-spec? (:ps args-spect))
                 (assoc spect :ret (reduce merge-keys (:ps args-spect)))
                 spect)))


(ann-method
 clojure.lang.Util 'identical (c/cat- [(c/class-spec Object) (c/class-spec Object)])
 (fn [spect args-spect]
   (let [x (-> args-spect c/first* maybe-convert-value)
         y (-> args-spect c/second* maybe-convert-value)
         ret (cond
               (and (c/value? x) (c/value? y)) (if (= (:v x) (:v y))
                                                 (c/value true)
                                                 (c/value false))
               (and (not= :ambiguous (c/truthyness x)) (not= :ambiguous (c/truthyness y))
                    (not= (c/truthyness x) (c/truthyness y))) (c/value false))]
     (if ret
       (assoc spect :ret ret)
       spect))))

(defn ann-get [spect args-spect]
  (let [coll (c/first* args-spect)
        key (c/second* args-spect)
        not-found (c/nth* args-spect 2)
        ret (cond
              (and (c/keys-spec? coll) (c/value? key) (keyword? (:v key))) (or (c/keys-get coll (:v key)) not-found)
              :else (:ret spect))]
    (assoc spect :ret ret)))

(ann-method clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object) (c/class-spec Object)]) ann-get)
(ann-method clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object)]) ann-get)

(def transducer-fn-spec (c/fn-spec nil nil nil))

(ann #'identity (fn [spect args-spect]
                  (assoc spect :ret (c/first* args-spect))))

(ann #'with-meta (fn [spect args-spect]
                   (assoc spect :ret (c/first* args-spect))))

(defn empty-seq?
  "True if this spect represents the empty seq, or a value that (seq x) would return nil on"
  [s]
  (or (c/valid? (c/value []) s)
      (c/valid? (c/value nil) s)
      (c/valid? (c/pred-spec #'nil?) s)))

(defn filter-fn [spect args-spect]
  (let [f (c/first* args-spect)
        coll (c/second* args-spect)]
    (if (and f (c/fn-spec? f) (c/coll-of? coll) (every? #(not (c/invalid? (c/invoke f (c/cat- [%])))) (c/all-possible-values coll)))
      (assoc spect :ret (c/coll-of (c/and-spec [(:s coll) (c/pred-spec (:var f))]) (:kind coll)))
      (c/invalid {:message (format "filter f does not conform: %s w/ %s" (print-str f) (print-str (first (filter (fn [arg]
                                                                                                                   (c/invalid? (c/invoke f (c/cat- [arg])))) (c/all-possible-values coll)))))
                  :form `(filter ~f ~coll)}))))

(defn ann-filter [spect args-spect]
  (if (= 1 (flow/cat-count args-spect))
    (assoc spect :ret transducer-fn-spec)
    (let [f (c/first* args-spect)
          coll (c/second* args-spect)]
      (cond
        (nil? coll) transducer-fn-spec
        (c/equivalent? coll (c/value nil)) (assoc spect :ret (c/value '()))
        (c/first-rest? coll) (filter-fn spect args-spect)
        :else spect))))

(ann #'filter ann-filter)

(defn map-coll-arity
  "Given the seq of collections passed to map, return the spec that will be passed to f"
  [colls]
  (->> colls
       (c/all-possible-values)
       (mapv (fn [colls*]
               (->> colls*
                    (mapv (fn [c]
                            (if-let [items (seq (c/coll-items c))]
                              (c/or- items)
                              (c/value nil))))
                    (c/cat- ))))
       (c/or- )))

(s/fdef map-fn :args (s/cat :s c/invoke? :args ::c/spect) :ret c/fn-spec?)
(defn map-fn [spect args-spect]
  (let [f (c/first* args-spect)
        colls (c/rest* args-spect)]
    (let [invoke-args (map-coll-arity colls)]
      (if (every? (fn [colls*] (every? (fn [c] (not (empty-seq? c))) colls*)) (c/all-possible-values colls))
        (if (c/valid? (:args f) invoke-args)
          (assoc spect :ret (c/coll-of (c/invoke f invoke-args)))
          (c/invalid {:message (format "couldn't invoke %s w/ %s" (print-str f) (print-str colls))}))
        (assoc spect :ret (c/value []))))))

;; [[X->Y] [X] -> [Y]]
(defn map-ann [spect args-spect]
  (if (= 1 (flow/cat-count args-spect))
    (assoc spect :ret transducer-fn-spec)
    (let [f (c/first* args-spect)
          colls (c/rest* args-spect)
          _ (assert (c/cat-spec? colls))
          coll-count (count (:ps colls))]
      (if (pos? coll-count)
        (cond
          (c/fn-spec? f) (map-fn spect args-spect)
          :else spect)
        (assoc spect :ret (c/value (list)))))))

(ann #'map map-ann)

;; [[X->[Y]] [X] -> [Y]]

(s/fdef mapcat-fn :args (s/cat :s c/fn-spec? :args ::c/spect) :ret c/fn-spec?)
(defn mapcat-fn [spect args-spect]
  (let [f (c/first* args-spect)
        colls (c/rest* args-spect)
        _ (assert (c/cat-spec? colls))
        colls (:ps colls)]
    (let [invoke-args (cond
                        (every? c/first-rest? colls) (c/cat- (map c/first* colls))
                        (every? c/value? colls) (let [colls (map :v colls)]
                                                            (when (seq colls)
                                                              (c/cat- (map (fn [p] (c/value (first (:v p)))) colls))))
                        :else (c/unknown {:message (format "mapcat-fn args unknown: %s" colls)
                                          :form args-spect}))]
      (if (every? (fn [c] (not (empty-seq? c))) colls)
        (if (and (c/conformy? (c/invoke f invoke-args))
                 (c/conform (c/pred-spec #'seqable?) (:ret f)))
          (assoc spect :ret (c/invoke f invoke-args))
          (do
            (c/invalid {:message (format "mapcat %s does not conform with %s" (print-str f) (print-str invoke-args))})))
        (do
          (assoc spect :ret (c/value [])))))))

;; [[X->Y] [X] -> [Y]]
(defn mapcat-ann [spect args-spect]
  (if (= 1 (flow/cat-count args-spect))
    (assoc spect :ret transducer-fn-spec)
    (let [f (c/first* args-spect)
          colls (c/rest* args-spect)
          _ (assert (c/cat-spec? colls))
          coll-count (count (:ps colls))]
      (if (pos? coll-count)
        (cond
          (c/fn-spec? f) (mapcat-fn spect args-spect)
          :else (do
                  ;;(println "ann map don't know how to check:" f)
                  spect))
        (assoc spect :ret (c/value (list)))))))

(ann #'any? (fn [spect args-spect]
              (assoc spect :ret (c/value true))))

(ann #'mapcat mapcat-ann)

(ann #'seq (fn [spect args-spect]
             (let [arg (c/first* args-spect)]
               (if (c/valid? (c/pred-spec #'seq?) arg)
                 (assoc spect :ret (c/pred-spec #'seq?))
                 spect))))

(def inc-ret-class {Long Long
                    Double Double
                    Float Double
                    BigInt BigInt
                    BigInteger BigInt
                    Ratio Ratio
                    BigDecimal BigDecimal})

(defn inc-transformer [spect args-spect]
  (let [arg (c/first* args-spect)]
    (if (c/valid? (c/class-spec Number) arg)
      (let [cs (c/spec->classes arg)
            ret (->> cs (map (fn [p] (get inc-ret-class p Long))) (distinct) (map c/class-spec) (c/or-))]
        (assoc spect :ret ret))
      (c/invalid {:message (format "inc: %s does not conform to Number" (print-str arg))}))))

(ann #'inc inc-transformer)
(ann-method clojure.lang.Numbers 'inc (c/cat- [(c/class-spec Object)]) inc-transformer)

(ann-protocol? #'c/spect? c/Spect)

(defn with-not-nil-ret
  "Given the spec for a java method, remove the (or nil) from the ret"
  [s args]
  (if (:ret s)
    (assoc-in s [:ret] (c/maybe-or-disj (:ret s) (c/value nil)))
    s))

(defn type-case
  "`case for conforming spects. Takes a seq with an even number of values. left hand side values must be spects. Finds the first left hand side value that x conforms to, returns the right-hand side. Throws on no match.

(type-case x
 (c/class-spec Long) :long
 (c/class-spec Double) :double)

"
  [x & ps]
  (assert (even? (count ps)))
  (let [ps (partition 2 ps)]
    (loop [[p & pr] ps]
      (if p
        (let [[spec val] p]
          (if (c/valid? spec x)
            val
            (recur pr)))
        (throw (ex-info "No matching clause" {:x x}))))))

(defn big-int? [x]
  (or (instance? clojure.lang.BigInt x)
      (instance? BigInteger x)))



(defn pred-count
  "Return the number of items in coll that conform to s"
  [s coll]
  (->> (map (fn [a] (c/valid? s a)) coll)
       (filter identity)
       count))

(s/fdef add-transform-concrete :args (s/cat :a class? :b class?) :ret class?)
(defn add-transform-singular [a b]
  (let [args [(c/class-spec a) (c/class-spec b)]
        int-count (pred-count (c/pred-spec #'int?) args)
        float-count (pred-count (c/pred-spec #'float?) args)
        big-int-count (pred-count (c/and-spec [(c/pred-spec #'integer?) (c/not-spec (c/pred-spec #'int?))]) args)
        big-dec-count (pred-count (c/pred-spec #'bigdec?) args)
        ratio-count (pred-count (c/pred-spec #'ratio?) args)]
    (cond
      (pos? float-count)  (c/class-spec Double/TYPE)
      (pos? big-dec-count) (c/class-spec BigDecimal)
      (pos? ratio-count) (c/class-spec Ratio)
      (pos? big-int-count) (c/class-spec BigInt)
      (= 2 int-count) (c/class-spec Long/TYPE)
      :else (c/class-spec Number))))

(defn add-transformer [spect args]
  (let [a (c/first* args)
        b (c/second* args)
        as (c/spec->classes a)
        bs (c/spec->classes b)
        ret (c/or- (set (for [a as
                              b bs]
                          (add-transform-singular a b))))]
    (assoc spect :ret ret)))

(ann-method clojure.lang.Numbers 'add (c/cat- [(c/class-spec Long) (c/class-spec Object)]) add-transformer)
(ann-method clojure.lang.Numbers 'add (c/cat- [(c/class-spec Object) (c/class-spec Long)]) add-transformer)
(ann-method clojure.lang.Numbers 'add (c/cat- [(c/class-spec Double/TYPE) (c/class-spec Object)]) add-transformer)
(ann-method clojure.lang.Numbers 'add (c/cat- [(c/class-spec Object) (c/class-spec Double/TYPE)]) add-transformer)
(ann-method clojure.lang.Numbers 'add (c/cat- [(c/class-spec Object) (c/class-spec Object)]) add-transformer)
