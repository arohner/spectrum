(ns spectrum.conform
  (:require [clojure.spec :as s]
            [clojure.set :as set]
            [spectrum.util :refer (fn-literal? literal?)]))

(defprotocol Spect
  (conform* [spec x]
    "True if value x conforms to spec."))

(defprotocol PredConform
  (pred-conform [this pred-s]
    "True if this spec conforms to the pred spec"))

(defprotocol AndConform
  (and-conform [this and-s]
    "True if this spec conforms to the And spec"))

(defprotocol OrConform
  (or-conform [this or-s]
    "True if this spec conforms with the Or spec passed in"))

(defprotocol RegexConform
  (regex-conform [spec seq]
    "True if this seq conforms to the spec"))

(defprotocol Regex
  (derivative
    [spec x]
    "Given a parsed spec, return the derivative")
  (empty-regex [this]
    "The empty pattern for this regex")
  (accept-nil? [this]
    "True if it is valid for this pattern to match no data")
  (return [this]
    "Given a completed regex parse, return the conform matching value")
  (add-return [this ret k]
    "Add ret to the return data of this regex, with optional key k"))

(defn regex? [x]
  (satisfies? Regex x))

(declare regex-accept)
(declare regex-reject)

(declare map->RegexAlt)

(defrecord RegexAccept [ret]
  Regex
  (derivative [spec x]
    regex-reject)
  (empty-regex [spec]
    regex-accept)
  (accept-nil? [this]
    true)
  (return [this]
    ret)
  (add-return [this ret k]
    ret))

(defn accept [x]
  (map->RegexAccept {:ret x}))

(defrecord RegexReject []
  Regex
  (derivative [spec x]
    nil)
  (empty-regex [spec]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    ::invalid)
  (add-return [this ret k]
    nil))

(defn regex-accept? [x]
  (instance? RegexAccept x))

(defn regex-reject? [x]
  (instance? RegexReject x))

(def regex-reject (map->RegexReject {}))

(extend-protocol Regex
  spectrum.conform.Spect
  (derivative [spec x]
    (if (conform* spec x)
      (map->RegexAccept {:ret x})
      regex-reject))
  (empty-regex [this]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    this)
  (add-return [this ret k]
    nil))

(extend-protocol Spect
  spectrum.conform.Regex
  (conform* [spec data]
    (if (or (nil? data) (coll? data))
      (let [[x & xs] data]
        (if (empty? data)
          (if (accept-nil? spec)
            (return spec)
            ::invalid)
          (if-let [dp (derivative spec x)]
            (recur dp xs)
            ::invalid)))
      ::invalid)))

(extend-protocol Regex
  nil
  (derivative [spec x]
    regex-reject)
  (empty-regex [spec]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    nil)
  (add-return [this ret k]
    nil))

(extend-protocol Regex
  Object
  (derivative [spec x]
    regex-reject)
  (empty-regex [spec]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    this)
  (add-return [this ret k]
    this))

(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  {:post [(do (println "maybe-alt" r1 r2 "=>" %) true )]}
  (if (and r1 r2 (not (regex-reject? r1)) (not (regex-reject? r2)))
    (map->RegexAlt {:ps [r1 r2]})
    (first (remove regex-reject? [r1 r2]))))

(declare map->RegexCat)

(s/fdef new-regex-cat :args (s/cat :ps (s/nilable coll?) :ks (s/nilable coll?) :fs (s/nilable coll?) :ret coll?) :ret regex?)

(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
  {:pre [(do (println "new-regex-cat:" [ps ks forms ret]) true )]
   :post [(do (println "new-regex-cat:" [ps ks forms ret] "=>" %) true )]}
  (if (every? #(not (regex-reject? %)) ps)
    (if (regex-accept? p0)
      (let [ret (conj ret (if k0 {k0 (:ret p0)} (:ret p0)))]
        (if pr
          (map->RegexCat {:ps pr
                          :ks kr
                          :forms fr
                          :ret ret})
          (accept ret)))

      (map->RegexCat {:ps ps
                      :ks ks
                      :forms forms
                      :ret ret}))
    regex-reject))

(defrecord RegexCat [ps ks forms ret]
  Regex
  (derivative [this x]
    (let [v (let [[p0 & pr] ps
                  [k0 & kr] ks
                  [f0 & fr] forms]
              (maybe-alt-
               (new-regex-cat (cons (derivative p0 x) pr) ks forms ret)
               (if (accept-nil? p0)
                 (derivative (new-regex-cat pr kr fr (add-return p0 ret k0)) x)
                 regex-reject)))]
      (println "cat derivative" this x "=>" v)
      v
      ))
  (accept-nil? [this]
    (every? accept-nil? ps))
  (return [this]
    (return (add-return (first ps) ret (first ks))))
  (add-return [this r k]
    (let [ret (return this)]
      (if (empty? ret)
        r
        (conj r (if k {k ret} ret))))))

(declare map->RegexSeq)

(defn new-regex-seq [ps ret splice forms]
  {:pre [(do (println "new-regex-seq:" ps) true )]
   :post [(do (println "new-regex-seq:" ps "=>" %) true )]}
  (if (every? #(not (regex-reject? %)) ps)
    (if (regex-accept? (first ps))
      (map->RegexSeq {:ps (rest ps)
                      :forms forms
                      :ret ((fnil conj []) ret (:ret (first ps)))
                      :splice splice})
      (map->RegexSeq {:ps ps
                      :forms forms
                      :ret ret
                      :splice splice}))
    regex-reject))

(defrecord RegexSeq [ps ks forms splice ret]
  Regex
  (derivative [this x]
    (new-regex-seq [(derivative (first ps) x) (first ps)] ret splice forms))
  (accept-nil? [this]
    true)
  (return [this]
    ret)
  (add-return [this r k]
    (let [ret (return this)]
      (if (empty? ret)
        r
        ((if splice into conj) r (if k {k ret} ret))))))

(defn filter-alt [ps ks forms f]
  (if (or ks forms)
    (let [pks (->> (map vector ps
                        (or (seq ks) (repeat nil))
                        (or (seq forms) (repeat nil)))
                   (filter #(-> % first f)))]
      [(seq (map first pks)) (when ks (seq (map second pks))) (when forms (seq (map #(nth % 2) pks)))])
    [(seq (filter f ps)) ks forms]))

(defn new-regex-alt [ps ks forms]
  (let [[[p1 & pr :as ps] [k1 :as ks] forms] (filter-alt ps ks forms #(not (regex-reject? %)))]
    (when ps
      (let [ret (map->RegexAlt {:ps ps :ks ks :forms forms})]
        (if (nil? pr)
          (if k1
            (if (regex-accept? p1)
              (do
                (accept [k1 (:ret p1)]))
              ret)
            p1)
          ret)))))

(defrecord RegexAlt [ps ks forms ret]
  Regex
  (derivative [this x]
    (println "RegexAlt derivative" this x)
    (new-regex-alt (map #(derivative % x) ps) ks forms))

  (empty-regex [this]
    (map->RegexAlt {:ps (map empty-regex ps)
                    :ks ks
                    :forms forms}))
  (accept-nil? [this]
    (some accept-nil? ps))
  (return [this]
    (let [[[p0] [k0]] (filter-alt ps ks forms accept-nil?)
          r (if (nil? p0)
              nil
              (return p0))]
      (if k0
        [k0 r]
        r)))
  (add-return [this r k]
    (let [ret (return this)]
      (if (= ret ::nil)
        r
        (conj r (if {k ret} ret))))))

(declare new-regex-plus)

(defn parse-regex-dispatch [x]
  ;; could be evaled or form, so check both

  (cond
    (map? x) (:clojure.spec/op x)
    (seq? x) (first x)))

(defmulti parse-regex #'parse-regex-dispatch)

(defn parse-spec-dispatch [x]
  (cond
    (s/spec? x) :spec
    (s/regex? x) :spec-regex
    (symbol? x) :fn-sym
    (var? x) :var
    (= :clojure.spec/nil x) :clojure.spec/nil
    (fn-literal? x) :fn-literal
    (literal? x) :literal
    (vector? x) :coll
    (seq? x) (first x)
    :else (do (println "unknown:" x (class x)) (throw (Exception. (format "parse-spec unknown: %s" x))))))

(defmulti parse-spec* #'parse-spec-dispatch)

(defmethod parse-spec* :spec-regex [x]
  (parse-regex x))

(defmethod parse-spec* :literal [x]
  x)

(def regex-vars '#{clojure.spec/* clojure.spec/alt})

(defn parse-spec [x]
  (cond
    (s/spec? x) (parse-spec* x)
    (s/regex? x) (parse-spec* x)
    (and (symbol? x) (resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
    (= :clojure.spec/nil x) (parse-spec* x)
    (keyword? x) (parse-spec* (#'s/the-spec x))
    (#'s/named? x) (parse-spec* (s/spec x))
    (fn-literal? x) (parse-spec* x)
    (literal? x) x
    (vector? x) (parse-spec* x)
    (and (seq? x) (contains? regex-vars (first x))) (parse-regex x)
    :else (do (println "unknown:" x (class x))
              (throw (Exception. (format "unknown spec: %s" x))))))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defrecord PredSpec [pred form]
  Spect
  (conform* [spec x]
    (cond
      (satisfies? PredConform x) (do "x satisfies predconform" (pred-conform x spec))
      (literal? x) (when ((:pred spec) x) x)
      :else false))
  PredConform
  (pred-conform [this pred]
    (when (= (:form this) (:form pred))
      this))
  OrConform
  (or-conform [this or-s]
    (some (fn [[k f]]
            (when (conform* f this)
              [k this])) (map vector (:ks or-s) (:forms or-s)))))

(defmethod parse-spec* :fn-sym [x]
  (let [v (resolve x)]
    (assert v)
    (map->PredSpec {:pred v
                    :form (symbol (str (.ns v)) (str (.sym v)))})))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* :coll [x]
  (mapv parse-spec* x))

(defmethod parse-spec* 'clojure.core/fn [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (first x)))

(defmethod parse-regex :clojure.spec/pcat [x]
  (map->RegexCat {:ks (:ks x)
                  :ps (mapv (fn [[form pred]]
                                          (if (:clojure.spec/op pred)
                                            (parse-regex pred)
                                            (parse-spec form))) (map vector (:forms x) (:ps x)))
                  :forms (:forms x)
                  :ret (:ret x)}))

(defn parse-seq [x]
  (let [forms (if (vector? (:forms x))
                (:forms x)
                [(:forms x)])
        preds (mapv parse-spec forms)]
    (map->RegexSeq {:ks (:ks x)
                    :ps preds
                    :forms forms
                    :ret []
                    :splice (:splice x)})))

(defmethod parse-regex :clojure.spec/rep [x]
  (parse-seq x))

(defmethod parse-regex 'clojure.spec/* [x]
  (parse-seq x))

(defmethod parse-regex :clojure.spec/alt [x]
  ;; evaled alt
  (map->RegexAlt {:ks (:ks x)
                  :forms (:forms x)
                  :ps (map parse-spec (:forms x))}))

(defmethod parse-regex 'clojure.spec/alt [x]
  ;; literal alt form
  (let [pairs (partition 2 (rest x))
        ks (map first pairs)
        forms (map second pairs)
        ps (map parse-spec forms)]
    (map->RegexAlt {:ks ks
                    :forms forms
                    :ps ps})))

(defmethod parse-spec* :clojure.spec/nil [x]
  (accept ::nil))

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:forms and-s))
    x))

(defrecord AndSpec [forms]
  Spect
  (conform* [this x]
    (cond
      (satisfies? AndConform x) (and-conform this x)
      (literal? x) (and-conform-literal this x)))
  PredConform
  (pred-conform [this pred]
    (some (fn [s]
            (conform* pred s)) (:forms this)))
  AndConform
  (and-conform [this that]
    (let [this-specs (set (:forms this))
          that-specs (set (:forms that))]
      (when (= this-specs (set/intersection this-specs that-specs))
        this))))

(defmethod parse-spec* 'clojure.spec/and [x]
  (map->AndSpec {:forms (mapv (fn [f]
                                (parse-spec f)) (rest x))}))

(defn or-conform-literal [or-s x]
  (some (fn [[k f]]
          (when (conform* f x)
            [k x])) (map vector (:ks or-s) (:forms or-s))))

(defrecord OrSpec [forms]
  Spect
  (conform* [this x]
    (cond
      (satisfies? OrConform x) (or-conform x this)
      (literal? x) (or-conform-literal this x)))

  PredConform
  (pred-conform [this pred]
    (some (fn [s]
            (when (conform* pred s)
              s)) (:forms pred))))

(defmethod parse-spec* 'clojure.spec/or [x]
  (let [pairs (partition 2 (rest x))
        keys (mapv first pairs)
        forms (mapv second pairs)]
    (map->OrSpec {:ks keys
                  :forms (mapv (fn [f]
                                 (parse-spec f)) forms)})))

(defn parse-fn-spec [s]
  (-> s
      (update-in [:args] parse-spec)
      (update-in [:ret] parse-spec)
      (update-in [:fn] parse-spec)))

(extend-protocol Spect
  clojure.spec.Spec
  (conform* [spec x]
    (conform* (parse-spec spec) x)))

(extend-type clojure.spec.Spec
  Spect
  (conform* [spec x]
    (conform* (parse-spec* spec) x))
  PredConform
  (pred-conform [spec x]
    (pred-conform (parse-spec spec) x)))

(defmacro conform
  "Given a spec and args, return the conforming parse. Behaves the same way as s/conform, but args may be clojure literals, or specs, not variables that contain values.

If an arg is a spec, it is treated as a variable that conforms to the spec. pass ::unknown for an variable with no specs.

(conform 'user/defn [symbol? string? [] (+ 1 2)])
=> {:def/name 'user/defn

 "
  [spec args]
  `(let [parsed# (parse-spec ~spec)
         args# (parse-spec ~args)]
     (if-let [val# (conform* parsed# args#)]
       (if (= ::nil val#)
         nil
         val#)
       ::invalid)))

(s/instrument-ns 'spectrum.conform)
