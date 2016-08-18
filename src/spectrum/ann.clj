(ns spectrum.ann
  (:require [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]
            [spectrum.util :refer (print-once)]))

(s/def ::transformer (s/fspec :args (s/cat :spec ::c/spect :args-spec ::c/spect) :ret ::c/spect))

(s/fdef ann :args (s/cat :v var? :f ::transformer))
(defn ann
  "Register a spec transformer. Takes a var or clojure.reflect.Method, and a transformer function

  ransformer function: a function taking 2 args: the function's spect,
  and the Spect for the fn args at this callsite. Returns an updated
  spec. This is typically used to make :ret more specific.
"
  [v f]
  (swap! data/spec-transformers assoc v f)
  nil)

(ann #'instance? (fn [spect args-spect]
                   (let [c (c/maybe-class (c/first* args-spect))
                         inst-spec (c/second* args-spect)
                         inst-cls (if (satisfies? c/SpecToClass inst-spec)
                                    (c/spec->class inst-spec)
                                    nil)]
                     (if inst-spec
                       (if inst-cls
                         (if (c/known? inst-spec)
                           (if (isa? inst-cls c)
                             (assoc spect :ret (c/value true))
                             (assoc spect :ret (c/value false)))
                           spect)
                         (do
                           (println "Can't spec->class:" inst-spec "Consider using ann/instance-transformer" )
                           spect))
                       (do
                         (print-once "No spec for:" inst-spec)
                         spect)))))

(ann #'into (fn [spect args-spect]
              (let [to (c/first* args-spect)
                    from (c/second* args-spect)]
                (if (c/known? to)
                  (assoc spect :ret to)
                  spect))))

(s/fdef instance-transformer :args (s/cat :c class?) :ret ::transformer)
(defn instance-transformer
  "Returns a spec-transformer for a simple (instance? c x) spec."
  [cls]
  (fn [spect args-spect]
    (let [arg (if (satisfies? c/FirstRest args-spect)
                (c/first* args-spect)
                args-spect)
          c (if (c/spect? arg)
              (c/spec->class arg)
              (class arg))]
      (if c
        (if (isa? c cls)
          (assoc spect :ret (c/value true))
          (assoc spect :ret (c/value false)))
        spect))))

(defn satisfies-transformer [protocol]
  (fn [spect args-spect]
    {:post [(do (println "satisfies:" args-spect "=>" %) true)]}
    (let [arg (if (satisfies? c/FirstRest args-spect)
                (c/first* args-spect)
                args-spect)
          c (if (c/spect? arg)
              (c/spec->class arg)
              (class arg))]
      (if c
        (if (satisfies? protocol c)
          (assoc spect :ret (c/value true))
          (assoc spect :ret (c/value false)))
        spect))))

(defn instance-or
  "spec-transformer for (or (instance? a) (instance? b)...) case. classes is a seq of classes."
  [classes]
  (fn [spect args-spect]
    (let [c (if (c/spect? args-spect)
              (c/spec->class (if (c/regex? args-spect)
                               (c/first* args-spect)
                               args-spect))
              (class args-spect))]
      (if c
        (if (some (fn [cls] (isa? c cls)) classes)
          (assoc spect :ret (c/value true))
          (assoc spect :ret (c/value false)))
        spect))))

(def pred->class
  {#'associative? clojure.lang.Associative
   #'bigdec java.math.BigDecimal
   #'boolean? Boolean
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

(doseq [[v cls] pred->class]
  (data/register-pred->class v cls)
  (ann v (instance-transformer cls)))

(ann #'int? (instance-or [Long Integer Short Byte]))
(ann #'integer? (instance-or [Long Integer Short Byte clojure.lang.BigInt BigInteger]))
(ann #'seqable? (instance-or [clojure.lang.ISeq clojure.lang.Seqable Iterable CharSequence java.util.Map])) ;; TODO java array

(defn maybe-convert-value
  "If the spect checks for a single value, i.e. nil? false?, return the value instead"
  [s]
  (if (c/pred-spec? s)
    (condp = (:pred s)
      #'nil? (c/value nil)
      #'false? (c/value false)
      #'true? (c/value true)
      s)
    s))

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
                                (every? (fn [v] (c/conform #'keyword? v)) (:v select)))
                         (let [vals (get-cat-vals (:v select))]
                           (let [ret (c/keys-spec (select-keys (:req m) vals)
                                                  (select-keys (:req-un m) vals)
                                                  (select-keys (:opt m) vals)
                                                  (select-keys (:opt-un m) vals))]
                             (assoc spect :ret ret)))
                         spect))))

(ann (flow/get-method! clojure.lang.Util 'identical (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
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


(s/fdef merge-keys :args (s/cat :m1 c/keys-spec? :m2 c/keys-spec?) :ret c/keys-spec?)
(defn merge-keys [m1 m2]
  (apply c/keys-spec (for [k [:req :req-un :opt :opt-un]]
                       (merge (get m1 k) (get m2 k)))))

(ann #'merge (fn [spect args-spect]
               (assert (c/cat-spec? args-spect))
               (if (every? c/keys-spec? (:ps args-spect))
                 (assoc spect :ret (reduce merge-keys (:ps args-spect)))
                 spect)))

(ann (flow/get-method! clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
     (fn [spect args-spect]
       (let [coll (c/first* args-spect)
             key (c/second* args-spect)
             ret (cond
                   (and (c/keys-spec? coll) (c/value? key)) (or (c/keys-get coll (:v key)) (c/pred-spec #'any?))
                   :else (:ret spect))]
         (assoc spect :ret ret))))

(ann (flow/get-method! clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object) (c/class-spec Object)]))
     (fn [spect args-spect]
       (let [coll (c/first* args-spect)
             key (c/second* args-spect)
             not-found (c/nth* args-spect 2)
             ret (cond
                   (and (c/keys-spec? coll) (c/value? key)) (or (c/keys-get coll key) not-found)
                   :else (:ret spect))]
         (assoc spect :ret ret))))

(def transducer-fn-spec (c/fn-spec nil nil nil))

(ann #'identity (fn [spect args-spect]
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
    (if (and (c/fn-spec? f) (flow/var-predicate? (:var f)) (c/coll-of? coll))
      (assoc spect :ret (c/coll-of (c/and-spec [(:s coll) (c/pred-spec (:var f))]) (:kind coll)))
      spect)))


(defn ann-filter [spect args-spect]
  (if (= 1 (flow/cat-count args-spect))
    (assoc spect :ret transducer-fn-spec)
    (let [f (c/first* args-spect)
          colls (c/rest* args-spect)
          _ (assert (c/cat-spec? colls))
          colls (:ps colls)
          coll-count (count (:ps colls))]
      (if (every? (fn [c] (not (empty-seq? c))) colls)
        (cond
          (c/fn-spec? f) (filter-fn spect args-spect)
          :else (do
                  ;;(println "ann filter don't know how to check:" f)
                  spect))
        (assoc spect :ret (c/value (list)))))))

(ann #'filter ann-filter)

(s/fdef map-fn :args (s/cat :s c/fn-spec? :args ::c/spect) :ret c/fn-spec?)
(defn map-fn [spect args-spect]
  (let [f (c/first* args-spect)
        colls (c/rest* args-spect)
        _ (assert (c/cat-spec? colls))
        colls (:ps colls)]
    (let [invoke-args (cond
                        (every? c/first-rest? colls) (c/cat- (map c/first* colls))
                        (every? c/value? colls) (let [colls (map :v colls)]
                                                            (when (seq colls)
                                                              (c/cat- (map (fn [p] (c/value (first (:v p)))) colls))))
                        :else (c/unknown args-spect))]
      (if (every? (fn [c] (not (empty-seq? c))) colls)
        (if (c/valid? (:args f) invoke-args)
          (if-let [v (:var f)]
            (assoc spect :ret (c/coll-of (:ret (c/maybe-transform v invoke-args))))
            spect)
          (assoc spect :ret c/reject))
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
          :else (do
                  (println "ann map don't know how to check:" f)
                  spect))
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
                        :else (do
                                (println "mapcat-fn args unknown:" colls)
                                (c/unknown args-spect)))]
      (if (every? (fn [c] (not (empty-seq? c))) colls)
        (if (and (c/valid? (:args f) invoke-args)
                 (c/conform (c/pred-spec #'seqable?) (:ret f)))
          (if-let [v (:var f)]
            (assoc spect :ret (:ret (c/maybe-transform v invoke-args)))
            (do
              ;;(println "ann mapcat-fn: default" f)
              spect))
          (do
            ;;(println "mapcat reject""" (:ret f))
            (assoc spect :ret c/reject)))
        (assoc spect :ret (c/value []))))))

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

(ann #'mapcat mapcat-ann)

(ann #'seq (fn [spect args-spect]
             (let [arg (c/first* args-spect)]
               (if (c/valid? (c/pred-spec #'seq?) arg)
                 (assoc spect :ret (c/pred-spec #'seq?))
                 spect))))
