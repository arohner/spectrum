(ns spectrum.conform
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.util :refer (fn-literal? literal? print-once strip-namespace var-name)]
            [spectrum.data :as data]
            [spectrum.java :as j])
  (:import (clojure.lang Var Keyword)
           java.io.Writer))

(declare valid?)
(declare parse-spec)
(declare conform)
(declare value)
(declare value?)

(declare and-spec?)
(declare class-spec?)
(declare keys-spec?)
(declare or-spec?)
(declare pred-spec?)
(declare unknown?)
(declare regex?)

(declare or-spec)
(declare class-spec)
(declare keys-spec)
(declare pred-spec)
(declare spect-generator)
(declare maybe-transform-pred)
(declare conform-args?)

(defprotocol Spect
  (conform* [spec x]
    "True if value x conforms to spec.")
  (explain* [spec path via in x]))

(defprotocol Compound
  (map- [spec f])
  (filter- [spec f]))

(defprotocol DependentSpecs
  (dependent-specs* [spec]))

(defn map* [f spec]
  (map- spec f))

(defn filter* [f spec]
  (filter- spec f))

(defn remove* [f spec]
  (filter- spec (complement f)))

(defn spect? [x]
  (and (map? x) (instance? clojure.lang.IRecord x) (satisfies? Spect x)))

(defprotocol WillAccept
  (will-accept [spec]
    "Returns a value that will make (derivative spec x) return accept"))

(s/fdef spec->class :args (s/cat :s ::spect) :ret (s/nilable ::j/java-type))
(defprotocol SpecToClass
  (spec->class [s]
    "If this spec checks for an instance of a class, return it, else nil"))

(defprotocol RegexConform
  (regex-conform [spec seq]
    "True if this seq conforms to the spec"))

(defprotocol Regex
  (derivative
    [spec x]
    "Given a parsed spec, return the derivative")
  (re-explain* [spec path via in x])
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

(defprotocol Truthyness
  (truthyness [this]
    "The truthyness of this spec, if it appeared in an `if`. Returns :truthy, :falsey or :ambiguous"))

(s/def ::spect (s/with-gen (s/and spect? map?)
                 (fn []
                   spect-generator)))

(s/fdef conform* :args (s/cat :spec spect? :x any?))

(defrecord Unknown [form file line column]
  Spect
  (conform* [this x]
    false)
  Truthyness
  (truthyness [this]
    :ambiguous))

(defn unknown
  ([form]
   (map->Unknown {:form form}))
  ([form a-loc]
   (map->Unknown (merge {:form form} a-loc))))

(defn unknown? [x]
  (instance? Unknown x))

(defn known? [x]
  (not (unknown? x)))

(defn first-rest? [x]
  (satisfies? FirstRest x))

(defn maybe-first* [ps]
  (if (first-rest? ps)
    (first* ps)
    (first ps)))

(defn maybe-rest* [ps]
  (if (first-rest? ps)
    (rest* ps)
    (rest ps)))

(defn second* [ps]
  (first* (rest* ps)))

(defn nth* [ps i]
  (if (and (seq ps) (not (neg-int? i)))
    (if (= 0 i)
      (first* ps)
      (recur (rest* ps) (dec i)))
    nil))

(s/fdef regex? :args (s/cat :x any?) :ret boolean?)

(defn regex? [x]
  (and (spect? x) (satisfies? Regex x) (or (:ps x) (:ret x))))

(declare accept)
(declare reject)

(declare map->RegexAlt)

(defrecord Accept [ret]
  Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    accept)
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
  (map->Accept {:ret x}))

(defrecord Reject []
  Regex
  (derivative [spec x]
    nil)
  (empty-regex [spec]
    reject)
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
    nil)
  Truthyness
  (truthyness [this]
    :falsey)
  SpecToClass
  (spec->class [this]
    nil))

(defn accept? [x]
  (instance? Accept x))

(defn reject? [x]
  (instance? Reject x))

(def reject (map->Reject {}))

(extend-protocol Regex
  spectrum.conform.Spect
  (derivative [spec x]
    (if (valid? spec x)
      (map->Accept {:ret x})
      reject))
  (empty-regex [this]
    reject)
  (accept-nil? [this]
    false)
  (return [this]
    this)
  (add-return [this ret k]
    nil))

(extend-type nil
  Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    reject)
  (accept-nil? [this]
    false)
  (return [this]
    ::s/nil)
  (add-return [this r k]
    r)
  FirstRest
  (first* [this]
    nil)
  (rest* [this]
    nil)
  Truthyness
  (truthyness [this]
    :falsey))

(extend-type Object
  Regex
  (derivative [spec x]
    (if (= spec x)
      (accept x)
      reject))
  (empty-regex [spec]
    reject)
  (accept-nil? [this]
    false)
  (return [this]
    this)
  (add-return [this ret k]
    this)
  WillAccept
  (will-accept [this]
    this)
  Truthyness
  (truthyness [this]
    :ambiguous))

(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  (if (and r1 r2 (not (reject? r1)) (not (reject? r2)))
    (map->RegexAlt {:ps [r1 r2]})
    (first (remove reject? [r1 r2]))))

(declare map->RegexCat)

(s/def :cat/ks (s/nilable (s/coll-of keyword?)))
(s/def :cat/ps (s/coll-of ::spect))
(s/def :cat/fs (s/nilable coll?))
(s/def :cat/ret coll?)

(s/fdef map->RegexCat :args (s/cat :x (s/keys :opt-un [:cat/ks :cat/ps :cat/fs] :req-un [:cat/ret])) :ret regex?)

(s/fdef new-regex-cat :args (s/cat :ps (s/nilable (s/coll-of (s/nilable ::spect))) :ks (s/nilable (s/coll-of keyword?)) :fs (s/nilable coll?) :ret coll?) :ret regex?)

(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
  (if (and ps
           (every? #(not (reject? %)) ps)
           (every? identity ps))
    (if (accept? p0)
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
    reject))

(s/fdef cat- :args (s/cat :ps (s/coll-of any?)))
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
                 reject)))]
      v))

  (re-explain* [spec path via in x]
    (let [pkfs (map vector
                    ps
                    (or (seq ks) (repeat nil))
                    (or (seq forms) (repeat nil)))
          [pred k form] (if (= 1 (count pkfs))
                          (first pkfs)
                          (first (remove (fn [[p]] (accept-nil? p)) pkfs)))
          path (if k (conj path k) path)]
      (if (and (empty? x) (not pred))
        [{:path path
          :reason "Insufficient input"
          :pred pred
          :val ()
          :via via
          :in in}]
        (explain* pred path via in x))))

  (accept-nil? [this]
    (every? accept-nil? ps))
  (return [this]
    (return (add-return (first ps) ret (first ks))))
  (add-return [this r k]
    (let [ret (return this)]
      (if (empty? ret)
        r
        (conj r (if k {k ret} ret)))))
  WillAccept
  (will-accept [this]
    (if-let [p (first ps)]
      (will-accept p)
      nil))
  FirstRest
  (first* [this]
    (let [p (first ps)]
      (if (and (and (first-rest? p) (regex? p)))
        (first* p)
        p)))
  (rest* [this]
    (let [dx (derivative this (will-accept this))]
      (if (not (accept? dx))
        dx
        nil)))
  Truthyness
  (truthyness [this]
    :truthy))

(s/fdef cat-spec? :args (s/cat :x any?) :ret boolean?)
(defn cat-spec? [x]
  (instance? RegexCat x))

(s/fdef cat-spec :args (s/cat :ks (s/* keyword?) :ps (s/* any?)) :ret cat-spec?)
(defn cat-spec [ks ps]
  (new-regex-cat ps ks nil []))

(declare map->RegexSeq)

(defn new-regex-seq [ps ret splice forms]
  (if (every? #(not (reject? %)) ps)
    (if (accept? (first ps))
      (map->RegexSeq {:ps (vec (rest ps))
                      :forms forms
                      :ret ((fnil conj []) ret (:ret (first ps)))
                      :splice splice})
      (map->RegexSeq {:ps (vec ps)
                      :forms forms
                      :ret ret
                      :splice splice}))
    reject))

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
  FirstRest
  (first* [this]
    (first ps))
  (rest* [this]
    (derivative this (will-accept this)))
  WillAccept
  (will-accept [this]
               (will-accept (first ps)))
  Truthyness
  (truthyness [this]
    :truthy)
  SpecToClass
  (spec->class [this]
    clojure.lang.ISeq)
  DependentSpecs
  (dependent-specs* [this]
    #{(pred-spec #'seq?) (pred-spec #'seqable?)}))

(defn filter-alt [ps ks forms f]
  (if (or ks forms)
    (let [pks (->> (map vector ps
                        (or (seq ks) (repeat nil))
                        (or (seq forms) (repeat nil)))
                   (filter #(-> % first f)))]
      [(seq (map first pks)) (when ks (seq (map second pks))) (when forms (seq (map #(nth % 2) pks)))])
    [(seq (filter f ps)) ks forms]))

(defn new-regex-alt [ps ks forms]
  (let [[[p1 & pr :as ps] [k1 :as ks] forms] (filter-alt ps ks forms #(not (reject? %)))]
    (when ps
      (let [ret (map->RegexAlt {:ps ps :ks ks :forms forms})]
        (if (nil? pr)
          (if k1
            (if (accept? p1)
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
  (re-explain* [spec path via in x]
    (if (empty? x)
      [{:path path
        :reason "Insufficient input"
        :val ()
        :via via
        :in in}]
      (apply concat
             (map (fn [k form p]
                    (explain* p
                              (if k (conj path k) path)
                              via
                              in
                              x))
                  (or (seq ks) (repeat nil))
                  (or (seq forms) (repeat nil))
                  ps))))

  FirstRest
  (first* [this]
    (first ps))
  (rest* [this]
    (derivative this (will-accept this)))
  WillAccept
  (will-accept [this]
    (will-accept (first ps)))
  Truthyness
  (truthyness [this]
    (let [b (distinct (map truthyness ps))]
      (if (= 1 (count b))
        (first b)
        :ambiguous))))

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
    (keyword? x) :keyword
    (and (seq? x) (symbol? (first x))) (first x)
    (coll? x) :coll
    (class? x) :class
    :else :literal))

(defmulti parse-spec* #'parse-spec*-dispatch)

(defmethod parse-spec* :literal [x]
  (if (spect? x)
    x
    (value x)))

(defmethod parse-spec* :class [x]
  (class-spec x))

(defn maybe-resolve [x]
  (try
    (resolve x)
    (catch Exception e
      nil)))

(defn parse-spec [x]
  (try
    (cond
      (spect? x) x
      (and (symbol? x) (maybe-resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
      (var? x) (parse-spec* (s/spec-impl (var-name x) x nil nil))
      (= ::s/nil x) ::s/nil
      (s/spec? x) (parse-spec* (s/form x))
      (s/regex? x) (parse-spec* x)
      :else (parse-spec* x))
    (catch IllegalArgumentException e
      (println "don't know how to parse:" x)
      (throw e))))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defmethod parse-spec* :keyword [x]
  (if (and (qualified-keyword? x) (s/get-spec x))
    (parse-spec (s/get-spec x))
    (value x)))

(defrecord Value [v]
  Spect
  (conform* [this x]
    (if (and (value? x) (= (:v this) (:v x)))
      x
      false))
  SpecToClass
  (spec->class [this]
    (class (:v this)))
  Truthyness
  (truthyness [this]
    (if v
      :truthy
      :falsey)))

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

(defn maybe-strip-value [x]
  (if (value? x)
    (:v x)
    x))

(s/fdef conformy? :args (s/cat :x any?) :ret boolean?)
(defn conformy?
  "True if the conform result returns anything other than ::invalid or reject"
  [x]
  (and (not= ::invalid x)
       (not (reject? x))))

(defrecord PredSpec [pred form]
  Spect
  (conform* [spec x]
    (let [ret (when (spect? x)
                (maybe-transform-pred spec x))
          truthy (= :truthy (truthyness ret))]
      (cond
        truthy x
        (= #'any? pred) x
        (and (pred-spec? x) (= pred (:pred x))) x
        (and (not (spect? x)) (conform-args? spec x)) (when ((:pred spec) x)
                                                        x)
        (class-spec? x) (when-let [pred-class (spec->class spec)]
                          (when (isa? pred-class (:cls x))
                            x))
        (and (satisfies? DependentSpecs x) (some (fn [px] (= spec px)) (dependent-specs* x))) x
        (satisfies? SpecToClass x) (conform* spec (class-spec (spec->class x))))))
  (explain* [spec path via in x]
    (when (not (valid? spec x))
      [{:path path :pred form :val x :via via :in in}]))
  WillAccept
  (will-accept [this]
    pred)
  Truthyness
  (truthyness [this]
    (condp = pred
      #'boolean? :ambiguous
      #'false? :falsey
      #'nil? :falsey
      #'any? :ambiguous
      :truthy)))

(s/fdef pred-spec :args (s/cat :v var?) :ret ::spect)
(defn pred-spec [v]
  (map->PredSpec {:pred v
                  :form (var-name v)}))

(s/fdef pred-spec? :args (s/cat :x any?) :ret boolean?)
(defn pred-spec? [x]
  (instance? PredSpec x))

(defn resolve-pred-spec
  "If spec is a PredSpec, find and parse its fnspec"
  [s]
  (if (pred-spec? s)
    (let [fnspec (s/get-spec (:pred s))]
      (when fnspec
        (let [fnspec (parse-spec fnspec)]
          (if (var? (:pred s))
            (assoc fnspec :var (:pred s))
            fnspec))))
    s))

(s/fdef any-spec? :args (s/cat :s pred-spec?) :ret boolean?)
(defn any-spec?
  "To prevent infinite recursion, recognize if this is the 'any? spec, and return true"
  [pred-spec]
  (-> pred-spec :form (= '(clojure.core/fn [x] (do true)))))

(extend-protocol DependentSpecs
  PredSpec
  (dependent-specs* [this]
    (loop [ret #{}
           spec this]
      (let [spec-fn (resolve-pred-spec spec)
            spec-arg (-> spec-fn :args (first*))]
        (if (and spec-fn (not (any-spec? spec-arg)))
          (do
            (recur (conj ret spec-arg) spec-arg))
          ret)))))

(defrecord FnSpec [args ret fn]
  Spect
  (conform* [this x]
    (if (and (fn-spec? x)
             (conform (:args this) (:args x))
             (conform (:ret this) (:ret x)))
      x
      false))
  (explain* [spec path via in x]
    (when-not (valid? spec x)
      [{:path path :pred spec :val x :via via :in in}]))
  SpecToClass
  (spec->class [this]
    clojure.lang.IFn))

(s/fdef fn-spec? :args (s/cat :x any?) :ret boolean?)
(defn fn-spec? [x]
  (instance? FnSpec x))

(s/fdef fn-spec :args (s/cat :args (s/nilable ::spect) :ret (s/nilable ::spect) :fn (s/nilable ::spect)))
(defn fn-spec [args ret fn]
  (map->FnSpec {:args args
                :ret ret
                :fn fn}))

(s/fdef get-var-fn-spec :args (s/cat :v var?) :ret (s/nilable fn-spec?))
(defn get-var-fn-spec [v]
  (when-let [s (s/get-spec v)]
    (assoc (parse-spec s) :var v)))

(s/fdef maybe-transform :args (s/cat :v (s/or :v var? :m j/reflect-method?) :args-spec ::spect) :ret (s/nilable fn-spec?))
(defn maybe-transform
  "apply the var's spec transformer, if applicable"
  [v args-spec]
  (when-let [fn-spec (get-var-fn-spec v)]
    (if-let [t (data/get-transformer v)]
      (let [fn-spec* (t fn-spec args-spec)]
        fn-spec*)
      fn-spec)))

(defn maybe-transform-method
  "apply the java method transformer, if applicable"
  [meth spec args-spec]
  (if-let [t (data/get-transformer meth)]
    (let [spec* (t spec args-spec)]
      spec*)
    spec))

(s/fdef conform-args :args (s/cat :s pred-spec? :x any?) :ret boolean?)
(defn conform-args?
  "True if x conforms to the :args of the pred's fn, i.e. it's valid to call the fn with x as args"
  [pred-spec x]
  (if (any-spec? pred-spec)
    true
    (let [fnspec (resolve-pred-spec pred-spec)]
      (if fnspec
        (if fnspec
          (valid? (:args fnspec) (cat- [x]))
          false)
        (println "no fnspec for:" pred-spec)))))

(s/fdef maybe-transform-pred :args (s/cat :s pred-spec? :arg (s/nilable ::spect)))
(defn maybe-transform-pred
  "maybe-transform the pred-spec, return its updated :ret, or nil"
  [pred-spec arg]
  (let [s (resolve-pred-spec pred-spec)
        v (:pred pred-spec)
        t (data/get-invoke-transformer v)]
    (if (not (reject? arg))
      (if s
        (let [ret (:ret s)
              ret* (:ret (maybe-transform v (cat- [arg])))]
          (if (not= ret ret*)
            ret*
            nil))
        (when (and t (not s))
          (println "warning: transformer but no spec for" v))))))

;; Spec representing a java class. Probably won't need to use this
;; directly. Used in java interop, and other places where we don't
;; have 'real' specs

(defrecord ClassSpec [cls]
  Spect
  (conform* [this v]
    (cond
      (satisfies? Spect v) (let [v-class (or (spec->class v) Object)]
                               (when (isa? v-class cls)
                                 v))
      (class? v) (isa? cls v)
      (j/primitive? v) (isa? cls (j/primitive->class v))
      (literal? v) (when (isa? cls (class v))
                     v)
      :else false))
  WillAccept
  (will-accept [this]
    cls)
  Truthyness
  (truthyness [this]
    (condp = (:cls this)
      Boolean :ambiguous
      nil :falsey
      :truthy)))

(defn class-spec [c]
  (map->ClassSpec {:cls c}))

(s/fdef class-spec :args (s/cat :x any?) :ret boolean?)
(defn class-spec? [x]
  (instance? ClassSpec x))

(defn maybe-class [x]
  (cond
    (class-spec? x) (:cls x)
    (class? x) x
    :else nil))

(defmethod parse-spec* :fn-sym [x]
  (let [v (resolve x)]
    (assert v)
    (map->PredSpec {:pred v
                    :form (symbol (str (.ns ^Var v)) (str (.sym ^Var v)))})))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defn parse-spec-seq [x]
  (let [v (mapv parse-spec* x)]
    (if (list? x)
      (value (list* v))
      (value (into (or (empty x) []) v)))))

(defn parse-spec-map [x]
  (let [state (reduce (fn [state [k v]]
                        (cond
                          (qualified-keyword? k) (assoc-in state [:req k] (parse-spec v))
                          (simple-keyword? k) (assoc-in state [:req-un k] (parse-spec v)))) {:req {}
                                                                                             :req-un {}} x)]
    (apply keys-spec [(:req state) (:req-un state) {} {}])))

(defmethod parse-spec* :coll [x]
  (cond
    (sequential? x) (parse-spec-seq x)
    (map? x) (parse-spec-map x)))

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
  (accept (:ret x)))

(defmethod parse-spec* 'clojure.spec/cat [x]
  (let [pairs (->> x rest (partition 2))
        ks (map first pairs)
        ps (map second pairs)]
    (map->RegexCat {:ks ks
                    :ps (mapv parse-spec ps)
                    :forms ps
                    :ret {}})))

(defmethod parse-spec* 'clojure.spec/fspec [x]
  (let [pairs (->> x rest (partition 2))
        pairs (map (fn [[k p]]
                     (when p
                       [k (parse-spec p)])) pairs)
        args (into {} pairs)]
    (map->FnSpec args)))

(defmethod parse-spec* :clojure.spec/rep [x]
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
  (let [forms (if (vector? (:forms x))
                (:forms x)
                [(:forms x)])
        preds (mapv parse-spec forms)]
    (map->RegexSeq {:ks (:ks x)
                    :ps preds
                    :forms forms
                    :ret []
                    :splice (:splice x)})))

(defmethod parse-spec* 'clojure.spec/* [x]
  (let [forms (rest x)
        ps (map parse-spec forms)]
    (map->RegexSeq {:ps ps
                    :forms forms
                    :ret []
                    :splice false})))

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
  (map->RegexAlt {:ps [(parse-spec (second x)) (accept ::s/nil)]}))

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:ps and-s))
    x))

(defrecord AndSpec [ps]
  Spect
  (conform* [this x]
    (conform this x))
  DependentSpecs
  (dependent-specs* [spec]
    (apply set/union (map dependent-specs* ps)))
  WillAccept
  (will-accept [this]
    this)
  Truthyness
  (truthyness [this]
    (let [b (distinct (map truthyness ps))]
      (if (= 1 (count b))
        (first b)
        :ambiguous))))

(defn and-spec? [x]
  (instance? AndSpec x))

(s/fdef and-spec :args (s/cat :forms (s/coll-of ::spect)) :ret ::spect)
(defn and-spec [x]
  (let [ps (remove valuey? x)]
    (cond
      (>= (count ps) 2) (map->AndSpec {:ps ps})
      :else (first ps))))

(defmethod parse-spec* 'clojure.spec/and [x]
  (and-spec (mapv parse-spec (rest x))))

(defrecord OrSpec [ps ks]
  Spect
  (conform* [this x]
    (some (fn [[k p]]
            (when (valid? p x)
              (if k
                [k x]
                x))) (mapv vector (or ks (repeat nil)) ps)))
  DependentSpecs
  (dependent-specs* [spec]
    (apply set/intersection (map dependent-specs* ps)))
  WillAccept
  (will-accept [this]
    (first ps))
  Truthyness
  (truthyness [this]
    (let [b (distinct (map truthyness ps))]
      (if (= 1 (count b))
        (first b)
        :ambiguous)))
  Compound
  (map- [this f]
    (let [kps (->> (mapv vector (or ks (repeat nil)) ps)
                   (map (fn [[k p]]
                          [k (f p)])))]
      (or-spec (map first kps) (map second kps))))
  (filter- [this f]
    (let [kps (->> (mapv vector (or ks (repeat nil)) ps)
                   (filter (fn [[k p]]
                             (f p))))]
      (or-spec (map first kps) (map second kps)))))

(defn or-spec? [x]
  (instance? OrSpec x))

(defn or- [ps]
  (if (>= (count ps) 2)
    (map->OrSpec {:ps ps})
    (first ps)))

(defn or-spec [ks ps]
  (map->OrSpec {:ks ks
                :ps ps}))

(defn or-disj
  "Remove pred from the set of preds"
  [s pred]
  (filter* (fn [p]
             (= p pred)) s))

(s/fdef conform-keys-keys :args (s/cat :s ::keys-spec :x ::keys-spec) :ret any?)
(defn conform-keys-keys [this x]
  (when (and
         (keys-spec? x)
         ;; x keys conform to spec
         (every? (fn [[key spec]]
                   (valid? spec (get-in x [:req key]))) (:req this))
         (every? (fn [[key spec]]
                   (valid? spec (get-in x [:req-un (strip-namespace key)]))) (:req-un this))
         ;; x keys conform to their own spec
         (->> [:req :opt]
              (map (fn [key-type]
                     (get x key-type)))
              (apply concat)
              (every? (fn [[key val]]
                        (if (s/get-spec key)
                          (valid? (parse-spec key) val)
                          true)))))
    x))

(defn conform-keys-value [s x]
  (when (and
         (map? x)
         ;; x keys conform to spec
         (every? (fn [[key spec]]
                   (valid? spec (get x key))) (:req s))
         (every? (fn [[key spec]]
                   (valid? spec (get x (strip-namespace key)))) (:req-un s))
         (every? (fn [[key spec]]
                   (if-let [v (get x key)]
                     (valid? spec v)
                     true)) (:opt s))
         (every? (fn [[key spec]]
                   (if-let [v (get x (strip-namespace key))]
                     (valid? spec v)
                     true)) (:req-un s)))
    x))

(defn explain-keys [{:keys [req req-un] :as spec} path via in x]
  (if-not (conform (pred-spec #'keys-spec?) x)
    [{:path path :pred 'map? :val x :via via :in in}]
    (->>
     (concat (mapv (fn [[key spec]]
                     [key spec (get-in x [:req key])]) req)
             (mapv (fn [[key spec]]
                     [key spec (get-in x [:req (strip-namespace key)])]) req-un)
             (mapv (fn [[key spec]]
                     [key spec (get-in x [:req key])]) (:opt x))
             (mapv (fn [[key spec]]
                     [key spec (get-in x [:req (strip-namespace key)])]) (:opt-un x)))
     (mapv (fn [[key spec val]]
             (when-not (valid? spec val)
               (explain* spec (conj path key) via in val)))))))

(defrecord KeysSpec [req req-un opt opt-un]
  Spect
  (conform* [this x]
    (cond
      (keys-spec? x) (conform-keys-keys this x)
      (not (spect? x)) (conform-keys-value this x)))
  (explain* [spec path via in x]
    (explain-keys spec path via in x))
  WillAccept
  (will-accept [this]
    this)
  SpecToClass
  (spec->class [this]
    clojure.lang.PersistentHashMap)
  Truthyness
  (truthyness [this]
    :truthy))

(s/fdef keys-spec :args (s/cat :x any?) :ret boolean?)
(defn keys-spec? [x]
  (instance? KeysSpec x))

(s/def ::keys-spec keys-spec?)


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

(s/fdef keys-get :args (s/cat :ks keys-spec? :key keyword?) :ret (s/nilable any?))
(defn keys-get
  "clojure.core/get, for key-spec"
  [ks key]
  (some (fn [key-type]
          (get-in ks [key-type key])) [:req :req-un :opt :opt-un]))

(s/fdef conform-collof-coll :args (s/cat :collof ::spect :x (s/nilable coll?)))
(defn conform-collof-coll [collof x]
  {:pre [(not (spect? x))]}
  (when (and (or (nil? (:kind collof))
                 (= (empty (:kind collof))
                    (empty x)))
             (every? (fn [v]
                       (valid? (:s collof) v)) x))
    x))

(defrecord CollOfSpec [s kind]
  Spect
  (conform* [this x]
    (cond
      (instance? CollOfSpec x) (when (valid? s (:s x))
                                 x)
      (not (spect? x)) (conform-collof-coll this x)
      :else false))
  SpecToClass
  (spec->class [s]
    (or (class s) clojure.lang.PersistentList))
  FirstRest
  (first* [this]
    s)
  (rest* [this]
    this)
  Truthyness
  (truthyness [this]
    :truthy))

(s/fdef coll-of :args (s/cat :s ::spect :kind (s/? (s/nilable coll?))) :ret ::spect)
(defn coll-of
  ([s]
   (coll-of s nil))
  ([s kind]
   (map->CollOfSpec {:s s
                     :kind kind})))

(s/fdef coll-of? :args (s/cat :x any?) :ret boolean?)
(defn coll-of? [x]
  (instance? CollOfSpec x))

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
                  :ps (mapv parse-spec forms)})))

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

(defn merge-keys [ks]
  (map->KeysSpec (apply merge-with merge ks)))

(s/fdef conform-map-of :args (s/cat :m ::spect :v value?) :ret any?)
(defn conform-map-of [map-of v]
  (when (and (every? (fn [k]
                       (valid? (:ks map-of) k)) (keys (:v v)))
             (every? (fn [v]
                       (valid? (:vs map-of) v)) (vals (:v v))))
    v))

(defrecord MapOf [ks vs]
  Spect
  (conform* [this x]
    (cond
      (instance? MapOf x) (when (and (valid? ks (:ks x))
                                     (valid? vs (:vs x)))
                                 x)
      (value? x) (conform-map-of this x)
      :else false))
  SpecToClass
  (spec->class [s]
    clojure.lang.PersistentHashMap)
  ;; FirstRest
  ;; TODO need tuples
  ;; (first* [this]
  ;;   )
  ;; (rest* [this]
  ;;   this)
  Truthyness
  (truthyness [this]
    :truthy))

(defn map-of [key-pred val-pred]
  (map->MapOf {:ks key-pred
               :vs val-pred}))

(defmethod parse-spec* 'clojure.spec/map-of [x]
  (let [k (nth x 1)
        v (nth x 2)]
    (map-of (parse-spec k) (parse-spec v))))

(defmethod parse-spec* 'clojure.spec/merge [x]
  (merge-keys (map parse-spec (rest x))))

(defmethod parse-spec* 'clojure.spec/conformer [x]
  (value true))

(extend-protocol Spect
  clojure.spec.Spec
  (conform* [spec x]
    (conform* (parse-spec spec) (parse-spec x))))

(extend-type clojure.spec.Spec
  Spect
  (conform* [spec x]
    (conform* (parse-spec* spec) x)))

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
    (spec->class-seq (:ps s)))
  spectrum.conform.AndSpec
  (spec->class [s]
    (spec->class-seq (:ps s)))
  spectrum.conform.ClassSpec
  (spec->class [s]
    (:cls s))
  spectrum.conform.Unknown
  (spec->class [s]
    Object))

(defn re-conform [spec data]
  (let [data (maybe-strip-value data)]
    (if (or (nil? data) (sequential? data) (and (spect? data) (regex? data)))
      (let [[x & xs] (if (:ps data)
                       (:ps data)
                       data)]
        (if (or (and (not (spect? data)) (empty? data))
                (and (regex? data) (nil? (first* data))))
          (if (accept-nil? spec)
            (return spec)
            ::invalid)
          (if-let [dp (derivative spec x)]
            (recur dp xs)
            ::invalid)))
      ::invalid)))

(defn re-explain [spec path via in data]
  (loop [spec spec
         [x & xr :as data] data
         i 0]
    (if (empty? data)
      (if (accept-nil? spec)
        nil
        [{:path path :via via :in in :reason (format "insufficient input. Empty input but re expects: %s" spec) :i i}])
      (if-let [dp (derivative spec x)]
        (recur dp xr (inc i))
        (re-explain* spec path via (conj in i) data)))))

(extend-protocol Spect
  spectrum.conform.Regex
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x)))

(def spect-generator (gen/elements [(pred-spec #'int?) (class-spec Long) (value true) (value false) (unknown nil)]))

(defn conform-strategy [spec args]
  (let [spec-or (or-spec? spec)
        spec-and (and-spec? spec)
        args-or (or-spec? args)
        args-and (and-spec? args)]
    (cond
      (and spec-and args-and) :and-and
      (and spec-or args-or) :or-or
      ;; (and spec-and args-or) :and-or
      ;; (and args-or spec-and) :or-and
      spec-and :spec-and
      spec-or :simple ;;spec-or
      args-and :args-and
      args-or :args-or
      :else :simple)))

(defmulti conform-compound #'conform-strategy)

(defmethod conform-compound :and-and [spec args]
  (when (every? (fn [p]
                  (valid? p args)) (:ps spec))
    args))

(defmethod conform-compound :or-or [spec args]
  (when (every? (fn [arg]
                  (valid? spec arg)) (:ps args))
    args))

(defmethod conform-compound :spec-and [spec args]
  (when (every? (fn [p]
                  (valid? p args)) (:ps spec))
    args))

(defmethod conform-compound :args-and [spec args]
  (when (some (fn [arg]
                (valid? spec arg)) (:ps args))
    args))

(defmethod conform-compound :args-or [spec args]
  (when (every? (fn [arg]
                  (valid? spec arg)) (:ps args))
    args))

(defmethod conform-compound :simple [spec args]
  (conform* spec args))

(s/fdef conform :args (s/cat :spec (s/or :spec s/spec? :re s/regex? :spect ::spect) :args any?) :ret any?)
(defn conform
  "Given a spec and args, return the conforming parse. Behaves similar to s/conform, but args may be clojure literals, or specs, not variables that contain values.

If an arg is a spec, it is treated as a variable that conforms to the spec. pass ::unknown for an variable with no specs.

(conform 'user/defn [symbol? string? [] (+ 1 2)])
=> {:def/name 'user/defn

 "
  [spec args]
  (try
    (let [t (:transformer spec)
          spec (parse-spec spec)
          spec (if t
                 (t spec args)
                 spec)]
      (if-let [val (conform-compound spec args)]
        (if (= ::s/nil val)
          nil
          val)
        ::invalid))
    (catch Throwable e
      (println "conform: kaboom:" spec args (.getMessage e))
      (throw e))))

(defn valid? [spec x]
  (conformy? (conform spec x)))

(s/fdef valid-invoke? :args (s/cat :s fn-spec? :args ::spect) :ret boolean?)
(defn valid-invoke?
  "check that fnspec can be invoked w/ args"
  [spec args]
  (assert (fn-spec? spec))
  (valid? (:args spec) args))

(s/fdef valid-return? :args (s/cat :s ::spect :args ::spect) :ret boolean?)
(defn valid-return?
  "True if spec conforms, as a return value. Conform must return truthy c/value"
  [spec args]
  (valid? spec args))

(defn explain-data [spec x]
  (explain* spec [] [] [] x))

(defn explain-out [data])

(defn explain [spec args]
  (explain-data spec args))

(defmethod print-method Unknown [spec ^Writer w]
  (let [{:keys [file line column]} spec]
    (.write w (str "#Unknown[" (print-str (:form spec)) (when file
                                                          (str file line column)) "]"))))

(defn regex-print-method [re-name spec ^Writer writer]
  (.write writer (str "#" re-name "[" (str/join ", " (map print-str (:ps spec))) "]")))

(defmethod print-method RegexCat [v ^Writer w]
  (regex-print-method "Cat" v w))

(defmethod print-method RegexSeq [v ^Writer w]
  (regex-print-method "Seq" v w))

(defmethod print-method RegexAlt [v ^Writer w]
  (regex-print-method "Alt" v w))

(defmethod print-method Value [v ^Writer w]
  (.write w (format "#Value[%s]" (print-str (:v v)))))

(defmethod print-method PredSpec [v ^Writer w]
  (.write w (format "#Pred[%s]" (print-str (:form v)))))

(defmethod print-method ClassSpec [v ^Writer w]
  (.write w (format "#Class[%s]" (print-str (:cls v)))))

(defmethod print-method AndSpec [v ^Writer w]
  (.write w (format "#And[%s]" (str/join ", " (map print-str (:ps v))))))

(defmethod print-method OrSpec [v ^Writer w]
  (.write w (format "#Or[%s]" (str/join ", " (map print-str (:ps v))))))

(defmethod print-method KeysSpec [spec ^Writer w]
  (.write w (format "#Keys{%s}" (->> [:req :req-un :opt :opt-un]
                                          (map (fn [k]
                                                 [k (get spec k)]))
                                          (filter (fn [[k v]]
                                                    v))
                                          (map (fn [[key-type key-preds]]
                                                 (format "%s{%s}" key-type (->> key-preds
                                                                                (map (fn [[k v]]
                                                                                       (format "%s %s" k (print-str v))))
                                                                                (str/join " " )))))
                                          (str/join " ")))))

(defmethod print-method CollOfSpec [spec ^Writer w]
  (.write w (let [[open close] (condp = (:kind spec)
                                      map? ["{" "}"]
                                      vector? ["[" "]"]
                                      set? ["#{" "}"]
                                      ["(" ")"])]
              (str "#CollOf "open  (print-str (:s spec))  close))))
