(ns spectrum.conform
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.util :refer (fn-literal? literal? print-once strip-namespace var-name)]
            [spectrum.data :as data]
            [spectrum.java :as j])
  (:import (clojure.lang Var Keyword)))

(declare valid?)
(declare parse-spec)
(declare conform)
(declare value)
(declare value?)
(declare fn-spec?)
(declare spect?)
(declare pred-spec?)
(declare and-spec?)
(declare or-spec?)
(declare keys-spec?)
(declare spect-generator)

(defprotocol Spect
  (conform* [spec x]
    "True if value x conforms to spec."))

(defn spect? [x]
  (and (map? x) (instance? clojure.lang.IRecord x) (satisfies? Spect x)))

(defprotocol SpectPrettyString
  (pretty-str [spec]))

(defprotocol WillAccept
  (will-accept [spec]
    "Returns a value that will make (derivative spec x) return accept"))

(s/fdef spec->class :args (s/cat :s ::spect) :ret (s/nilable ::j/java-type))
(defprotocol SpecToClass
  (spec->class [s]
    "If this spec checks for an instance of a class, return it, else nil"))

(defprotocol PredConform
  (pred-conform [this pred-s]
    "True if this conforms to the pred spec"))

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

(defprotocol FirstRest
  (first* [this])
  (rest* [this]))

(defn regex-pretty-str [re-name spec]
  (str "#" re-name "[" (str/join ", " (map pretty-str (:ps spec))) "]"))

(s/def ::spect (s/with-gen (s/and spect? map?)
                 (fn []
                   spect-generator)))

(s/def ::args ::spect)
(s/def ::ret ::spect)
(s/def ::fn ::spect)

(s/def ::fn-spect #'fn-spec?)

(s/def ::error #(= % ::invalid))

(s/fdef conform* :args (s/cat :spec spect? :x any?))

(defrecord Unknown [form file line column]
  Spect
  (conform* [this x]
    false)
  SpectPrettyString
  (pretty-str [x]
    (str "#Unknown[" (pretty-str form) (when file
                                         (str file line column)) "]")))

(defn unknown
  ([form]
   (map->Unknown {:form form}))
  ([form a-loc]
   (map->Unknown (merge {:form form} a-loc))))

(defn unknown? [x]
  (instance? Unknown x))

(defn known? [x]
  (not (unknown? x)))

(defn maybe-first* [ps]
  (if (satisfies? FirstRest ps)
    (first* ps)
    (first ps)))

(defn maybe-rest* [ps]
  (if (satisfies? FirstRest ps)
    (rest* ps)
    (rest ps)))

(defn second* [ps]
  (first* (rest* ps)))

(s/fdef regex? :args (s/cat :x any?) :ret boolean?)

(defn regex? [x]
  (and (spect? x) (satisfies? Regex x) (or (:ps x) (:ret x))))

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
    ret)
  WillAccept
  (will-accept [this]
    nil)
  FirstRest
  (first* [this]
    nil)
  (rest* [this]
    nil))

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
    nil)
  WillAccept
  (will-accept [this]
    nil)
  FirstRest
  (first* [this]
    nil)
  (rest* [this]
    nil))

(defn regex-accept? [x]
  (instance? RegexAccept x))

(defn regex-reject? [x]
  (instance? RegexReject x))

(def regex-reject (map->RegexReject {}))

(extend-protocol Regex
  spectrum.conform.Spect
  (derivative [spec x]
    (let [v (conform* spec x)]
      (if (and v (or (not (value? v))
                     (and (value? v) (:v v))))
        (map->RegexAccept {:ret x})
        regex-reject)))
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
    (if (or (nil? data) (coll? data) (spect? data))
      (let [[x & xs] (if (:ps data)
                       (:ps data)
                       data)]
        (if (empty? data)
          (if (accept-nil? spec)
            (return spec)
            ::invalid)
          (if-let [dp (derivative spec x)]
            (recur dp xs)
            ::invalid)))
      ::invalid)))

(extend-type nil
  Regex
  (derivative [spec x]
    regex-reject)
  (empty-regex [spec]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    ::s/nil)
  (add-return [this r k]
    r)
  SpectPrettyString
  (pretty-str [x]
    "nil")
  FirstRest
  (first* [this]
    nil)
  (rest* [this]
    nil))

(extend-type Object
  Regex
  (derivative [spec x]
    (if (= spec x)
      (accept x)
      regex-reject))
  (empty-regex [spec]
    regex-reject)
  (accept-nil? [this]
    false)
  (return [this]
    this)
  (add-return [this ret k]
    this)
  WillAccept
  (will-accept [this]
    this)
  SpectPrettyString
  (pretty-str [x]
    (str x)))

(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  (if (and r1 r2 (not (regex-reject? r1)) (not (regex-reject? r2)))
    (map->RegexAlt {:ps [r1 r2]})
    (first (remove regex-reject? [r1 r2]))))

(declare map->RegexCat)

(s/fdef new-regex-cat :args (s/cat :ps (s/nilable coll?) :ks (s/nilable coll?) :fs (s/nilable coll?) :ret coll?) :ret regex?)

(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
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

(defn cat- [ps]
  (new-regex-cat ps nil nil []))

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
      v))

  (accept-nil? [this]
    (every? accept-nil? ps))
  (return [this]
    (return (add-return (first ps) ret (first ks))))
  (add-return [this r k]
    (let [ret (return this)]
      (if (empty? ret)
        r
        (conj r (if k {k ret} ret)))))
  SpectPrettyString
  (pretty-str [this]
    (regex-pretty-str "Cat" this))
  WillAccept
  (will-accept [this]
    (will-accept (first ps)))
  FirstRest
  (first* [this]
    (let [p (first ps)]
      (if (satisfies? FirstRest p)
        (first* p)
        p)))
  (rest* [this]
    (derivative this (parse-spec (will-accept this)))))

(s/fdef cat-spec :args (s/cat :x any?) :ret boolean?)
(defn cat-spec? [x]
  (instance? RegexCat x))

(declare map->RegexSeq)

(defn new-regex-seq [ps ret splice forms]
  (if (every? #(not (regex-reject? %)) ps)
    (if (regex-accept? (first ps))
      (map->RegexSeq {:ps (vec (rest ps))
                      :forms forms
                      :ret ((fnil conj []) ret (:ret (first ps)))
                      :splice splice})
      (map->RegexSeq {:ps (vec ps)
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
        ((if splice into conj) r (if k {k ret} ret)))))
  SpectPrettyString
  (pretty-str [this]
    (regex-pretty-str "Seq" this))
  FirstRest
  (first* [this]
    (first ps))
  (rest* [this]
    (derivative this (will-accept this)))
  WillAccept
  (will-accept [this]
    (will-accept (first ps))))

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
      (if (= ret ::s/nil)
        r
        (conj r (if {k ret} ret)))))
  SpectPrettyString
  (pretty-str [this]
    (regex-pretty-str "Alt" this))
  FirstRest
  (first* [this]
    (first ps))
  (rest* [this]
    (derivative this (will-accept this)))
  WillAccept
  (will-accept [this]
    (will-accept (first ps))))

(declare new-regex-plus)

(defn get-spec [spec-name]
  (let [s (s/get-spec spec-name)
        cs (parse-spec s)]
    (if-let [t (data/get-transformer spec-name)]
      (assoc cs :transformer t)
      cs)))

(defn parse-spec*-dispatch [x]
  (cond
    (s/spec? x) :spec
    (s/regex? x) (:clojure.spec/op x)
    (spect? x) :literal
    (symbol? x) :fn-sym
    (var? x) :var
    (fn-literal? x) :fn-literal
    (and (seq? x) (symbol? (first x))) (first x)
    (coll? x) :coll
    :else :literal))

(defmulti parse-spec* #'parse-spec*-dispatch)

(defmethod parse-spec* :literal [x]
  x)

(defn parse-spec [x]
  (cond
    (spect? x) x
    (and (symbol? x) (resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
    (var? x) (parse-spec* (s/spec-impl (var-name x) x nil nil))
    (= ::s/nil x) ::s/nil
    (and (keyword? x)) (parse-spec* (#'s/the-spec x))
    (#'s/named? x) (parse-spec* (s/spec x))
    (s/spec? x) (parse-spec* (s/form x))
    (s/regex? x) (parse-spec* x)
    :else (parse-spec* x)))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defrecord Value [v]
  Spect
  (conform* [this x]
    (if (and (value? x) (= (:v this) (:v x)))
      x
      false))
  SpecToClass
  (spec->class [this]
    (class (:v this)))
  PredConform
  (pred-conform [this pred-s]
    (when ((:pred pred-s) (:v this))
      this))
  SpectPrettyString
  (pretty-str [x]
    (str "#Value[" (pretty-str v) "]")))

(s/fdef value :args (s/cat :x any?) :ret value?)
(defn value
  "spec representing a single value"
  [v]
  (map->Value {:v v}))

(s/fdef value? :args (s/cat :x any?) :ret boolean?)
(defn value? [s]
  (instance? Value s))

(s/fdef valuey? :args (s/cat :x any?) :ret boolean?)
(defn valuey? [s]
  "true if s is a value with a truthy value"
  (and (value? s) (boolean (:v s))))

(s/fdef conformy? :args (s/cat :x any?) :ret boolean?)
(defn conformy?
  "True if the conform result returns anything other than ::invalid or (c/value falsey)"
  [x]
  (if (value? x)
    (boolean (:v x))
    (not= ::invalid x)))

(defn resolve-pred-spec
  "If spec is a PredSpec, find and parse its fnspec"
  [s]
  (if (pred-spec? s)
    (let [fnspec (s/get-spec (:pred s))]
      (when fnspec
        (parse-spec fnspec)))
    s))

(s/fdef maybe-transform :args (s/cat :v var? :fn-spec ::spect :args-spec ::spect) :ret ::fn-spect)
(defn maybe-transform
  "apply the var's spec transformer, if applicable"
  [v fn-spec args-spec]
  (if-let [t (data/get-transformer v)]
    (let [_ (when-not (s/valid? ::fn-spect fn-spec)
              (println "invalid fn-spec:" v fn-spec)
              (println (s/explain ::fn-spect fn-spec)))
          _ (assert (s/valid? ::fn-spect fn-spec))
          fn-spec* (t fn-spec args-spec)]
      fn-spec*)
    fn-spec))

(s/fdef conform-spec-ret :args (s/cat :s pred-spec? :arg any?))
(defn conform-spec-ret
  "Check that fnspec, a predicate, returns truthy when called w/ arg. Returns a c/value or c/unknown"
  [fnspec arg]
  (let [s (resolve-pred-spec fnspec)]
    (if s
      (let [v (:pred fnspec)
            ret (:ret (maybe-transform v s arg))]
        (if (value? ret)
          ret
          false))
      (do
        (println "conform-spec-ret: ret spec not spec'd" fnspec)
        (unknown nil)))))

(defrecord PredSpec [pred form]
  Spect
  (conform* [spec x]
    (cond
      (satisfies? PredConform x) (or (pred-conform x spec) (conform-spec-ret spec x))
      (= x pred) x
      (literal? x) (when ((:pred spec) x) x)
      :else (conform-spec-ret spec x)))
  PredConform
  (pred-conform [this pred]
    (when (= (:form this) (:form pred))
      this))
  OrConform
  (or-conform [this or-s]
    (some (fn [[k f]]
            (when (conform* f this)
              (if k
                [k this]
                this))) (map vector (or (:ks or-s) (repeat nil)) (:forms or-s))))
  SpectPrettyString
  (pretty-str [this]
    (str form))
  WillAccept
  (will-accept [this]
    pred))

(s/fdef pred-spec :args (s/cat :v var?) :ret ::spect)
(defn pred-spec [v]
  (map->PredSpec {:pred v
                  :form (var-name v)}))

(defn pred-spec? [x]
  (instance? PredSpec x))

;; Spec representing a java class. Probably won't need to use this
;; directly. Used in java interop, and other places where we don't
;; have 'real' specs

(defrecord ClassSpec [cls]
  Spect
  (conform* [this v]
    (cond
      (and-spec? v) (when (some (fn [p]
                                  (isa? (spec->class p) cls)) (:forms v))
                      v)
      (or-spec? v) (when (every? (fn [p]
                                   (conformy? (conform this p))) (:forms v))
                     v)
      (satisfies? Spect v) (let [v-class (or (spec->class v) Object)]
                               (when (isa? v-class cls)
                                 this))
      (class? v) (isa? cls v)
      (j/primitive? v) (isa? cls (j/primitive->class v))
      (literal? v) (when (isa? cls (class v))
                     v)
      :else false))
  PredConform
  (pred-conform [this pred-s]
    (when-let [pred-class (spec->class pred-s)]
      (when (isa? pred-class cls)
        pred-s)))
  AndConform
  (and-conform [this and-s]
    (when (some (fn [p]
                  (conformy? (conform p this))) (:forms and-s))
      this))
  SpectPrettyString
  (pretty-str [this]
    (str cls))
  WillAccept
  (will-accept [this]
    cls))

(defn class-spec [c]
  (map->ClassSpec {:cls c}))

(defmethod parse-spec* :fn-sym [x]
  (let [v (resolve x)]
    (assert v)
    (map->PredSpec {:pred v
                    :form (symbol (str (.ns ^Var v)) (str (.sym ^Var v)))})))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* :coll [x]
  (let [v (mapv parse-spec* x)]
    (if (list? x)
      (list* v)
      (into (or (empty x) []) v))))

(defmethod parse-spec* 'clojure.core/fn [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (first x)))

(defmethod parse-spec* 'var [x]
  (parse-spec* (second x)))

(defmethod parse-spec* :clojure.spec/pcat [x]
  (map->RegexCat {:ks (:ks x)
                  :ps (mapv (fn [[form pred]]
                              (parse-spec (if (:clojure.spec/op pred)
                                            pred
                                            form))) (map vector (:forms x) (:ps x)))
                  :forms (:forms x)
                  :ret (:ret x)}))

(defmethod parse-spec* :clojure.spec/accept [x]
  (map->RegexAccept {:ret (:ret x)}))

(defmethod parse-spec* 'clojure.spec/cat [x]
  (let [pairs (->> x rest (partition 2))
        ks (map first pairs)
        ps (map second pairs)]
    (map->RegexCat {:ks ks
                    :ps (mapv parse-spec ps)
                    :forms ps
                    :ret {}})))

(defrecord FnSpec [args ret fn]
  Spect
  (conform* [this x]
    (if (and (fn-spec? x)
             (conform (:args this) (:args x))
             (conform (:ret this) (:ret x)))
      x
      false)))

(s/fdef fn-spec? )
(defn fn-spec? [x]
  (instance? FnSpec x))

(defmethod parse-spec* 'clojure.spec/fspec [x]
  (let [pairs (->> x rest (partition 2))
        pairs (map (fn [[k p]]
                     [k (parse-spec p)]) pairs)
        args (into {} pairs)]
    (map->FnSpec args)))

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

(defmethod parse-spec* :clojure.spec/rep [x]
  (parse-seq x))

(defmethod parse-spec* 'clojure.spec/* [x]
  (parse-seq x))

(defmethod parse-spec* :clojure.spec/alt [x]
  ;; evaled alt
  (let [pairs (map vector (:ps x) (:forms x))
        forms (map (fn [[p f]]
                    (if (fn? p)
                      f
                      p)) pairs)]

    (map->RegexAlt {:ks (:ks x)
                    :forms (:forms x)
                    :ps (mapv parse-spec forms)})))

(defn parse-literal-alt [x]
  (let [pairs (partition 2 (rest x))
        ks (mapv first pairs)
        forms (mapv second pairs)
        ps (mapv parse-spec forms)]
    (map->RegexAlt {:ks ks
                    :forms forms
                    :ps ps})))

(defmethod parse-spec* 'clojure.spec/alt [x]
  ;; literal alt form
  (parse-literal-alt x))

(defmethod parse-spec* 'clojure.spec/? [x]
  (parse-literal-alt x))

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:forms and-s))
    x))

(defrecord AndSpec [forms]
  Spect
  (conform* [this x]
    (cond
      (satisfies? AndConform x) (and-conform x this)
      (literal? x) (and-conform-literal this x)))
  PredConform
  (pred-conform [this pred]
    (when (some (fn [s]
                  (conform* pred s)) (:forms this))
      this))
  AndConform
  (and-conform [this that]
    (let [this-specs (set (:forms this))
          that-specs (set (:forms that))]
      (when (= that-specs (set/intersection this-specs that-specs))
        that)))
  WillAccept
  (will-accept [this]
    this)
  SpectPrettyString
  (pretty-str [x]
    (str "#And[" (str/join ", " (map pretty-str forms)) "]")))

(defn and-spec? [x]
  (instance? AndSpec x))

(s/fdef and-spec :args (s/cat :forms (s/coll-of ::spect)) :ret ::spect)
(defn and-spec [x]
  (let [forms (remove valuey? x)]
    (cond
      (>= (count forms) 2) (map->AndSpec {:forms forms})
      :else (first forms))))

(defmethod parse-spec* 'clojure.spec/and [x]
  (and-spec (mapv parse-spec (rest x))))

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
              s)) (:forms pred)))
  OrConform
  (or-conform [this spec]
    (assert (satisfies? OrConform spec))
    (when (= (set (:forms spec)) (set/intersection (set (:forms spec)) (set (:forms this))))
      this))
  WillAccept
  (will-accept [this]
    (first forms))
  SpectPrettyString
  (pretty-str [x]
    (str "#Or[" (str/join ", " (map pretty-str forms)) "]")))

(defn or-spec? [x]
  (instance? OrSpec x))

(defn or- [ps]
  (if (>= (count ps) 2)
    (map->OrSpec {:forms ps})
    (first ps)))



(s/fdef conform-keys-spec :args (s/cat :a spect? :b spect?) :ret (s/or :s spect? :err ::error))
(defn conform-keys-spec [a b]
  (when (and (= (set (:req a)) (set/intersection (set (:req a)) (set (:req b))))
             (= (set (:req-un a)) (set/intersection (set (:req-un a)) (set (:req-un b)))))
    b))

(defn conform-keys-literal [this x]
  (when (and
         (every? (fn [[key spec]]
                   (valid? spec (get x key))) (:req this))
         (every? (fn [[key spec]]
                   (valid? spec (get x (strip-namespace key)))) (:req-un this))
         (every? (fn [[key spec]]
                   (if (contains? x key)
                     (valid? spec (get x key))
                     true)) (:opt this))
         (every? (fn [[key spec]]
                   (if (contains? x (strip-namespace key))
                     (valid? spec (get x (strip-namespace key)))
                     true)) (:opt-un this)))
    x))

(defrecord KeysSpec [req req-un opt opt-un]
  Spect
  (conform* [this x]
    (cond
      (instance? KeysSpec x) (conform-keys-spec this x)
      (map? x) (conform-keys-literal this x)
      :else false))
  WillAccept
  (will-accept [this]
    this)
  SpectPrettyString
  (pretty-str [this]
    (str "(keys " (->> [:req :req-un :opt :opt-un]
                      (map (fn [k]
                             [k (get this k)]))
                      (filter (fn [[k v]]
                                v))
                      (map (fn [[k v]]
                             (str k (vec (keys v)))))
                      (str/join " ")) ")"))
  SpecToClass
  (spec->class [this]
    clojure.lang.PersistentHashMap))

(s/fdef keys-spec :args (s/cat :x any?) :ret boolean?)
(defn keys-spec? [x]
  (instance? KeysSpec x))

(s/fdef keys-spec :args (s/cat :req (s/nilable (s/map-of qualified-keyword? ::spect))
                               :req-un (s/nilable (s/map-of keyword? ::spect))
                               :opt (s/nilable (s/map-of qualified-keyword? ::spect))
                               :opt-un (s/nilable (s/map-of keyword? ::spect)))
        :ret keys-spec?)

(defn keys-spec [req req-un opt opt-un]
  (map->KeysSpec {:req req
                  :req-un (into {} (map (fn [[k s]]
                                          [(strip-namespace k) s]) req-un))
                  :opt opt
                  :opt-un (into {} (map (fn [[k s]]
                                          [(strip-namespace k) s]) opt-un))}))

(defrecord CollOfSpec [s kind]
  Spect
  (conform* [this x]
    (cond
      (instance? CollOfSpec x) (when (conformy? (conform s (:s x)))
                                x)
      :else false))
  SpecToClass
  (spec->class [s]
    (or (class s) clojure.lang.PersistentList)))

(defn parse-coll-of [x]
  (let [args (rest x)
        s (parse-spec (first args))
        opts (apply hash-map (rest args))]
    (map->CollOfSpec (merge {:s s} opts))))

(defmethod parse-spec* 'clojure.spec/every [x]
  (parse-coll-of x))

(defmethod parse-spec* 'clojure.spec/coll-of [x]
  (parse-coll-of x))

(defmethod parse-spec* 'clojure.spec/nilable [x]
  (let [s (parse-spec (second x))]
    (or- [s (parse-spec #'nil?)])))

(defmethod parse-spec* 'clojure.spec/or [x]
  (let [pairs (partition 2 (rest x))
        keys (mapv first pairs)
        forms (mapv second pairs)]
    (map->OrSpec {:ks keys
                  :forms (mapv parse-spec forms)})))

(defmethod parse-spec* 'clojure.spec/keys [x]
  (let [args (->> (rest x)
                  (partition 2)
                  (map (fn [[key-type specs]]
                         [key-type (into {} (map (fn [spec-name]
                                                   (if-let [s (s/get-spec spec-name)]
                                                     [spec-name (parse-spec (s/form s))]
                                                     (throw (Exception. (format "Could not resolve spec: %s" spec-name))))) specs))]))
                  (into {} ))]
    (keys-spec (:req args)
               (:req-un args)
               (:opt args)
               (:opt-un args))))

(defmethod parse-spec* 'clojure.spec/conformer [x]
  (value true))

(defn parse-fn-spec [s]
  {:args (-> s :args parse-spec)
   :ret (-> s :ret parse-spec)
   :fn (-> s :fn parse-spec)})

(extend-protocol Spect
  clojure.spec.Spec
  (conform* [spec x]
    (println "spect conform spec" spec x)
    (conform* (parse-spec spec) (parse-spec x))))

(extend-type clojure.spec.Spec
  Spect
  (conform* [spec x]
    (conform* (parse-spec* spec) x))
  PredConform
  (pred-conform [spec x]
    (pred-conform (parse-spec spec) x)))

(defn spec->class-seq [forms]
  (->> forms
       rest
       (map (fn [f]
              (let [a (spec->class (first forms))
                    b (spec->class f)]
                (when (and a b)
                  (j/shared-ancestors a b)))))
       (filter identity)
       (apply set/union)
       (first)))

(extend-protocol SpecToClass
  spectrum.conform.PredSpec
  (spec->class [s]
    (data/pred->class (:pred s)))
  spectrum.conform.OrSpec
  (spec->class [s]
    (spec->class-seq (:forms s)))
  spectrum.conform.AndSpec
  (spec->class [s]
    (spec->class-seq (:forms s)))
  spectrum.conform.ClassSpec
  (spec->class [s]
    (:cls s))
  spectrum.conform.Unknown
  (spec->class [s]
    Object))

(def spect-generator (gen/elements [(pred-spec #'int?) (class-spec Long) (value true) (value false) (unknown nil)]))

(defn conform
  "Given a spec and args, return the conforming parse. Behaves similar to s/conform, but args may be clojure literals, or specs, not variables that contain values.

If an arg is a spec, it is treated as a variable that conforms to the spec. pass ::unknown for an variable with no specs.

(conform 'user/defn [symbol? string? [] (+ 1 2)])
=> {:def/name 'user/defn

 "
  [spec args]
  (let [spec (parse-spec spec)
        args (parse-spec args)
        t (:transformer spec)
        spec (if t
               (t spec args)
               spec)]
    (if-let [val (conform* spec args)]
      (if (= ::s/nil val)
        nil
        val)
      ::invalid)))

(defn valid? [spec x]
  (not= ::invalid (conform spec x)))

(defn valid-invoke?
  "check that fnspec can be invoked w/ args"
  [spec args]
  (assert (fn-spec? spec))
  (conformy? (conform (:args spec) args)))

(defn valid-return?
  "True if spec conforms, as a return value. Conform must return truthy c/value"
  [spec args]
  (conformy? (conform spec args)))
