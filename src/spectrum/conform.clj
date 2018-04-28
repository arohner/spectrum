(ns spectrum.conform
  (:refer-clojure :exclude [seq?])
  (:require [clojure.core :as core]
            [clojure.core.memoize :as memo]
            [clojure.math.combinatorics :as combo]
            [clojure.reflect :as reflect]
            [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.gen]
            [spectrum.protocols :as p]
            [spectrum.util :refer [fn-literal? print-once strip-namespace var-name queue queue? predicate-spec validate! conj-seq multimethod-dispatch-values protocol?]]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.java :as j])
  (:import (clojure.lang Var Keyword IFn ISeq)
           java.io.Writer
           (spectrum.protocols Accept Reject Invalid Unknown Bottom ThrowForm RecurForm RegexCat RegexSeq RegexAlt Value AndSpec NotSpec OrSpec TupleSpec SpecSpec DelaySpec PredSpec ClassSpec ProtocolSpec KeysSpec CollOfSpec ArrayOf MapOf FnSpec MultiSpec)))

(declare conform)
(declare valid?)
(declare parse-spec)
(declare value)


(declare class-spec?)
(declare pred-spec?)
(declare or?)
(declare alt?)
(declare concrete?)

(declare class-spec)
(declare pred-spec)
(declare spect-generator)
(declare conform-pred-args?)

(declare value-invoke)
(declare value-invoke-accept)

(declare re-conform)
(declare re-explain)
(declare cat-)
(declare or-)

(declare maybe-or-disj)

(predicate-spec spect?)
(defn spect? [x]
  (and (instance? clojure.lang.IRecord x) (satisfies? p/Spect x)))


(s/fdef truthyness :args (s/cat :s ::spect) :ret #{:truthy :falsey :ambiguous})
(defn truthyness [s]
  {:post [(contains? #{:truthy :falsey :ambiguous} %)]}
  (p/truthyness s))

(s/def ::spect spect?)

(defn concrete? [x]
  (and (spect? x) (not (or? x)) (not (alt? x))))

(s/fdef conform* :args (s/cat :s ::spect :x any?) :ret (s/nilable ::spect))

(defn keys-get? [s]
  (satisfies? p/KeysGet s))

(defn dependent-specs? [s]
  (satisfies? p/DependentSpecs s))

(declare spec->classes)

(defn singular? [x]
  (not (p/regex? x)))

(s/def :with-return/ret (s/or :s (s/nilable ::spect) :coll (s/coll-of (s/or :s ::spect :ret :with-return/ret) :kind vector?)))

(s/fdef accept :args (s/cat :x (s/or :s ::spect :wr :with-return/ret)) :ret ::spect)
(defn accept [x]
  (p/map->Accept {:ret x}))

(def reject (p/map->Reject {}))

(defn accept? [x]
  (instance? Accept x))

(defn reject? [x]
  (instance? Reject x))

(s/fdef return :args (s/cat :s :with-return/ret) :ret (s/nilable ::spect))
(defn return [s]
  {:post [(validate! (s/nilable ::spect) %)]}
  (validate! (s/or :accept accept? :accept-nil p/accept-nil? :not-re singular?) s)
  (let [ret (p/return- s)]
    (validate! :with-return/ret ret)
    (if (vector? ret)
      (cat- (mapv return ret))
      ret)))

(s/fdef elements :args (s/cat :s ::spect) :ret (s/coll-of ::spect))
(defn elements [s]
  {:post [(validate! (s/coll-of ::spect) %)]}
  (p/elements s))

(defn fix-length
  "Given a regex possibly containing Seq, recursively resolve to
  all concrete specs of *up to* length n, i.e. (fix-length (s/+ int?) 2)
  -> [(cat) (cat int?) (cat int? int?)]. Should be performed after disentangle"
  [s n]
  {:post [(validate! (s/coll-of ::spect) %)
          (do (when (< (count %) 1)
                (println "fix-length failed:" s n "=>" %)) true)
          (>= (count %) 1)]}
  (p/fix-length s n))

(def ^:dynamic *disentangle-depth* 0)

(s/fdef disentangle :args (s/cat :s ::spect) :ret (s/coll-of ::spect))
(defn disentangle
  "Given a spec containing choices, such as `or` or `alt`, return a
  seq of concrete specs that don't contain choices"
  [s]
  {:pre [(spect? s)]
   :post [(validate! (s/coll-of ::spect) %)]}
  (if (< *disentangle-depth* 3)
    (binding [*disentangle-depth* (inc *disentangle-depth*)]
      (p/disentangle s))
    [s]))

(s/fdef with-return :args (s/cat :this (s/nilable ::spect) :ret :with-return/ret) :ret (s/nilable ::spect))
(defn with-return [s ret]
  {:post [(validate! :with-return/ret %)]}
  (p/with-return- s ret))

(s/def ::derivative-ret ::spect)
(s/fdef derivative :args (s/cat :s ::spect) :ret ::spect)
(defn derivative [s x]
  {:post [(do (when-not (s/valid? ::derivative-ret %) (println "invalid derivative:" s "=>" %)) true) (s/valid? ::derivative-ret %)]}
  (p/derivative s x))

(s/def ::will-accept-ret (s/nilable ::spect))
(s/fdef will-accept :args (s/cat :s ::spect) :ret ::spect)
(defn will-accept [s]
  {:post [(do (when-not (s/valid? ::will-accept-ret %) (println "invalid will-accept:" s "=>" %)) true) (s/valid? ::will-accept-ret %)]}
  (p/will-accept- s))

(s/fdef accept-nil? :args (s/cat :s ::spect) :ret boolean?)
(defn accept-nil? [s]
  {:post [(boolean? %)]}
  (p/accept-nil? s))

(s/fdef keys-get :args (s/cat :s ::spect :k keyword?) :ret ::spect)
(defn keys-get [s k]
  {:post [(s/valid? ::spect %)]}
  (if (keys-get? s)
    (p/keys-get- s k)
    (value nil)))

(s/fdef p/keyword-invoke- :args (s/cat :s ::spect :args ::spect) :ret ::spect)
(s/fdef keyword-invoke :args (s/cat :s ::spect :args ::spect) :ret ::spect)
(defn keyword-invoke [s args]
  {:post [(spect? %)]}
  (when-not (spect? (p/keyword-invoke- s args))
    (println "keyword-invoke:" s args "=>" (p/keyword-invoke- s args)))
  (p/keyword-invoke- s args))

(defn keyword-invoke? [s]
  (satisfies? p/KeywordInvoke s))

(predicate-spec invalid?)
(defn invalid? [x]
  (or (instance? Invalid x)
      (= ::invalid x)))

(s/fdef conformy? :args (s/cat :x any?) :ret boolean?)
(defn conformy?
  "True if the conform result returns anything other than invalid or reject"
  [x]
  (boolean (and x
                (not (invalid? x))
                (not (reject? x)))))

(s/def ::spect (s/and ::spect map?))
(s/def ::valid-spect (s/and ::spect conformy?))

(predicate-spec form?)
(defn form? [x]
  (and (sequential? x)
       (core/seq? x)
       (symbol? (first x))))

(defn spec-regex? [x]
  (and (map? x) (::s/op x)))

;; a thing that parse-spec will return a valid ::spect on
(s/def ::spect-like (s/or :spec s/spec? :spec-re spec-regex? :spect ::spect :key keyword? :sym symbol? :var var? :form form? :set set?))

(s/def ::valid-spect-like (s/or :spec s/spec? :spec-re spec-regex? :spect ::valid-spect :key keyword? :sym symbol? :var var? :form form? :set set?))

(s/fdef conform* :args (s/cat :spec ::spect :x any?))

(s/def :invalid/message string?)
(s/def :invalid/form any?)

(s/fdef invalid :args (s/cat :args (s/keys :req-un [:invalid/message] :opt-un [:invalid/form] )))
(defn invalid [{:keys [form a-loc message] :as args}]
  (let [a *a*
        form (if (find args form)
               form
               (:form *a*))
        a-loc (if (find args :a-loc)
                a-loc
                (select-keys (:meta *a*) [:file :line :column]))]
    (p/map->Invalid (merge args {:form form :a-loc a-loc :message message}))))

(extend-type Invalid
  p/Spect
  (conform* [this x]
    reject)
  p/Truthyness
  (truthyness [this]
    :ambiguous)
  p/WillAccept
  (will-accept- [this]
    reject))

(predicate-spec invoke?)
(defn invoke? [x]
  (satisfies? p/Invoke x))

(defn bottom? [x]
  (instance? Bottom x))

(extend-type Bottom
  p/Spect
  (conform* [this x]
    reject)
  p/Truthyness
  (truthyness [this]
    :falsey)
  p/WillAccept
  (will-accept- [this]
    reject))

(defn bottom [{:keys [form a-loc message] :as args}]
  (let [a *a*
        form (if (find args form)
               form
               (:form *a*))
        a-loc (if (find args :a-loc)
                a-loc
                (select-keys (:meta *a*) [:file :line :column]))]
    (p/map->Bottom (merge args {:form form :a-loc a-loc :message message}))))

(s/fdef invoke :args (s/cat :s ::spect :args ::spect) :ret ::spect)

(defn invoke [s args]
  {:pre [(validate! ::spect s)
         (validate! ::spect args)]
   :post [(validate! ::spect %)]}
  (if (invoke? s)
    (p/invoke- s args)
    (invalid {:message (format "invoke: %s doesn't implement Invoke" (print-str s))})))

(defn invoke-accept [s]
  {:pre [(validate! ::spect s)]
   :post [(validate! ::spect %)]}
  (if (invoke? s)
    (p/invoke-accept- s)
    (invalid {:message (format "invoke-accept: %s doesn't implement Invoke" (print-str s))})))

(s/fdef first-rest? :args (s/cat :x any?) :ret boolean?)
(defn first-rest? [x]
  (satisfies? p/FirstRest x))

(s/fdef first- :args (s/cat :x first-rest?) :ret any?)
(defn first- [x]
  (p/first- x))

(s/fdef rest- :args (s/cat :x first-rest?) :ret any?)
(defn rest- [x]
  (p/rest- x))

(defn maybe-first* [ps]
  (if (first-rest? ps)
    (p/first- ps)
    (first ps)))

(defn maybe-rest* [ps]
  (if (first-rest? ps)
    (p/rest- ps)
    (rest ps)))

(defn second- [ps]
  (first- (rest- ps)))

(defn nth* [ps i]
  (if (and (seq ps) (not (neg-int? i)))
    (if (= 0 i)
      (first- ps)
      (recur (rest- ps) (dec i)))
    nil))

(def first-rest-singular-impl
  {:first- (fn [this] reject)
   :rest- (fn [this] reject)})

(defn first-rest-singular
  "FirstRest implementation for a type that is singular"
  [s]
  (extend s p/FirstRest first-rest-singular-impl))

(declare reject)

(extend-type Accept
  p/Spect
  (conform* [spec x]
    (when (and (accept? x) (= (:ret spec) (:ret x)))
      x))
  p/Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    accept)
  (accept-nil? [this]
    true)
  (return- [this]
    (:ret this))
  (with-return- [this ret]
    ret)
  (regex? [this]
    false)
  (disentangle [this]
    [this])
  p/WillAccept
  (will-accept- [this]
    reject))

(first-rest-singular Accept)

(extend-type Reject
  p/Spect
  (conform* [spec x]
    reject)
  p/Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    reject)
  (accept-nil? [this]
    false)
  (return- [this]
    (invalid {:message "reject"}))
  (with-return- [this ret]
    reject)
  (regex? [this]
    false)
  (elements [this]
    [this])
  p/WillAccept
  (will-accept- [this]
    reject)
  p/Truthyness
  (truthyness [this]
    :falsey))

(first-rest-singular Reject)

(defn unknown? [x]
  (instance? Unknown x))

(s/fdef unknown :args (s/cat :args (s/keys :req-un [:invalid/message] :opt-un [:invalid/form])))
(defn unknown
  [{:keys [form a-loc message] :as args}]
  (let [a *a*
        form (if form
               form
               (:form *a*))
        a-loc (if a-loc
                a-loc
                (select-keys *a* [:file :line :column]))]
    (p/map->Unknown {:form form :a-loc a-loc :message message})))

(defn unknown-invoke [spec args]
  (unknown {:message (format "unknown-invoke: don't know how to invoke %s with %s" (print-str spec) (print-str args))}))

(extend-type Unknown
  p/Spect
  (conform* [this x]
    (when (unknown? x)
      x))
  p/Truthyness
  (truthyness [this]
    :ambiguous)
  p/WillAccept
  (will-accept- [this]
    this)
  p/Invoke
  (invoke- [spec args]
    (unknown-invoke spec args))
  (invoke-accept- [spec]
    (unknown {:message "invoke on unknown"}))
  p/FirstRest
  (first- [this]
    (unknown {:message "first on unknown"}))
  (rest- [this]
    (unknown {:message "rest on unknown"}))
  p/KeysGet
  (keys-get- [this k]
    (unknown {:message "get on unknown"})))

(defn known? [x]
  (not (unknown? x)))

(extend-type nil
  p/Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    reject)
  (accept-nil? [this]
    true)
  (return- [this]
    (value nil))
  (with-return- [this r]
    r)
  (regex? [this]
    false)
  p/Truthyness
  (truthyness [this]
    :falsey)
  p/FirstRest
  (first- [this]
    nil)
  (rest- [this]
    nil))

(extend-type Invalid
  p/Regex
  (derivative [spec x]
    reject)
  (empty-regex [spec]
    reject)
  (accept-nil? [this]
    false)
  (return- [this]
    (value nil))
  (with-return- [this r]
    r)
  (regex? [this]
    false)
  (elements [this]
    [this]))

(first-rest-singular Invalid)

(s/fdef spec-dx :args (s/cat :spec ::spect :x ::spect) :ret ::spect)
(defn spec-dx [spec x]
  (if (valid? spec x)
    (accept x)
    reject))

(extend-type Object
  p/Regex
  (return- [this]
    this)
  (regex? [this]
    false)
  (accept-nil? [this]
    false))

(def spect-regex-impl
  {:derivative spec-dx
   :disentangle (fn [this]
                  [this])
   :empty-regex (fn [this]
                  reject)
   :accept-nil? (fn [this]
                  false)
   :return- (fn [this]
              this)
   :with-return- (fn [this ret]
                   {:pre [(s/valid? (s/nilable sequential?) ret)]}
                   ret)
   :regex? (fn [this]
             false)
   :fix-length (fn [this n]
                 [this])
   :elements (fn [this]
               [this])})

(defn extend-regex
  "extends the Regex protocol to a non-regex Spect"
  [s]
  (extend s p/Regex spect-regex-impl))

(defn will-accept-this
  "extend the spec to WillAccept itself"
  [s]
  (extend s p/WillAccept {:will-accept- (fn [this] this)}))

(extend-regex Unknown)

(extend-type RecurForm
  p/Spect
  (conform* [this x]
    reject)
  p/Truthyness
  (truthyness [this]
    :ambiguous)
  p/WillAccept
  (will-accept- [this]
    reject))

(extend-regex RecurForm)

(extend-type ThrowForm
  p/Spect
  (conform* [this x]
    reject)
  p/Truthyness
  (truthyness [this]
    :ambiguous)
  p/WillAccept
  (will-accept- [this]
    reject))

(extend-regex ThrowForm)

(s/fdef recur? :args (s/cat :x any?) :ret boolean?)
(defn recur? [x]
  (instance? RecurForm x))

(defn recur-form [args]
  (p/map->RecurForm {:args args}))

(s/fdef throwable? :args (s/cat :x any?) :ret boolean?)
(defn throwable? [x]
  (instance? Throwable x))

(s/fdef throw? :args (s/cat :x any?) :ret boolean?)
(defn throw? [x]
  (instance? ThrowForm x))

(s/fdef throw-form :args (s/cat :e ::spect) :ret throw?)
(defn throw-form [e]
  (assert (spect? e))
  (p/map->ThrowForm {:s e}))

(s/fdef control-flow? :args (s/cat :x any?) :ret boolean?)
(defn control-flow? [x]
  (or (throw? x) (recur? x)))

(defn spect-or-control-flow? [x]
  (or (spect? x) (control-flow? x)))

(s/def ::dependent-specs (s/coll-of ::spect :kind set?))

(defn dependent-specs* [s]
  {:post [(validate! ::dependent-specs %)]}
  (if (dependent-specs? s)
    (p/dependent-specs- s)
    #{}))

(predicate-spec value?)
(defn value? [s]
  (instance? Value s))

(s/fdef value :args (s/cat :x any?) :ret value?)
(defn value
  "spec representing a single value"
  [v]
  (p/map->Value {:v v
                 ;; numbers of different type share same hash, store
                 ;; type so the values hash differently, because c/conform
                 ;; is cached
                 :type (when (number? v)
                         (class v))
                 }))

(defn maybe-strip-value [s]
  (if (value? s)
    (:v s)
    s))

(s/fdef get-value :args (s/cat :v value?) :ret any?)
(defn get-value [v]
  (:v v))

(extend-type Value
  p/Spect
  (conform* [this x]
    (cond
      (instance? Value x) (when (= (:v this) (:v x))
                            x)
      :else (when (= (:v this) x)
              x)))
  p/Truthyness
  (truthyness [this]
    (if (:v this)
      :truthy
      :falsey))
  p/Invoke
  (invoke- [this args]
    (value-invoke this args))
  (invoke-accept- [this]
    (value-invoke-accept this))
  p/KeywordInvoke
  (keyword-invoke- [this args]
    (let [key (first- args)
          else (second- args)
          rest (rest- (rest- args))]
      (cond
        (nil? key) (invalid {:message "not enough args"})
        rest (invalid {:message "value keyword invoke: too many args"})
        (and (value? key) (value? else)) (value (get (:v this) (:v key) (:v else)))
        (and (value? key) (nil? else)) (value (get (:v this) (:v key)))
        :else (unknown {:message "don't know how to keyword-invoke"}))))
  p/FirstRest
  (first- [{:keys [v] :as this}]
    (if (and v (or (core/seq? v) (seqable? v)))
      (if (seq v)
        (value (first v))
        nil)
      (invalid {:message (format "value %s does not support first" v)
                :form `(first ~v)})))
  (rest- [{:keys [v] :as this}]
    (if (or (core/seq? v) (seqable? v))
      (if (seq (rest v))
        (value (rest v))
        nil)
      (invalid {:message (format "value %s does not support rest" v) :form `(rest ~v)})))
  p/DependentSpecs
  (dependent-specs- [this]
    (if (nil? (:v this))
      #{}
      #{(class-spec (class (:v this)))}))
  p/WillAccept
  (will-accept- [this]
    this)
  p/KeysGet
  (keys-get- [{:keys [v] :as this} k]
    (if (coll? v)
      (value (get v k))
      (value nil))))

(extend-regex Value)

(s/fdef dependent-specs :args (s/cat :s (s/nilable ::spect)) :ret ::dependent-specs)
(defn dependent-specs [s]
  (set/union (dependent-specs* s) (data/get-dependent-specs s)))

(defn maybe-convert-value [x]
  (-> (dependent-specs x)
      (#(filter value? %))
      first
      (or x)))

(s/fdef recursive-dependent-specs :args (s/cat :s (s/nilable ::spect)) :ret ::dependent-specs)
(defn recursive-dependent-specs
  "Recursively resolve dependent-specs"
  [s]
  (loop [ret #{}
         seen #{}
         q (queue [s])]
    (if-let [s (first q)]
      (let [new (set/difference (dependent-specs s) seen)]
        (recur (set/union ret new) (conj seen s) (conj-seq (pop q) new)))
      ret)))

(s/def ::class-or (s/or :c class-spec? :or or?))

(s/fdef more-specfic-spec? :args (s/cat :a ::class-or :b ::class-or) :ret boolean?)
(defn more-specific-spec?
  [a b]
  (cond
    (or? a) (every? (fn [a*]
                      (more-specific-spec? a* b)) (:ps a))
    (or? b) (every? (fn [b*]
                      (more-specific-spec? a b*)) (:ps b))
    :else (do
            (when-not (and (class-spec? a) (class-spec? b))
              (println "more specific: a:" a "b:" b))
            (assert (class-spec? a))
            (assert (class-spec? b))
            (j/more-specific? (:cls a) (:cls b)))))

(s/fdef most-specific-specs :args (s/cat :specs (s/coll-of ::spect) :ret ::spect))
(defn most-specific-spec [specs]
  (reduce (fn [a b]
            (if (more-specific-spec? a b)
              a
              b)) (class-spec Object) specs))

(s/fdef maybe-alt- :args (s/cat :r1 (s/nilable ::spect) :r2 (s/nilable ::spect)) :ret ::spect)
(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  {:post [(spect? %)]}
  (if (and r1 r2 (every? conformy? [r1 r2]))
    (p/map->RegexAlt {:ps [r1 r2]})
    (or (first (filter conformy? [r1 r2]))
        reject)))

(s/def :cat/ks (s/nilable (s/coll-of keyword?)))
(s/def :cat/ps (s/coll-of ::spect-like))
(s/def :cat/fs (s/nilable coll?))
(s/def :cat/ret (s/coll-of (s/or :s ::spect-like :cat :cat/ret) :kind vector?))

(predicate-spec cat?)
(defn cat? [x]
  (instance? RegexCat x))

(s/fdef p/map->RegexCat :args (s/cat :x (s/keys :opt-un [:cat/ks :cat/ps :cat/fs] :req-un [:cat/ret])) :ret cat?)

(declare new-regex-cat )

(s/fdef cat- :args (s/cat :ps (s/coll-of ::spect-like :kind sequential? :gen-max 5)) :ret ::spect)
(defn cat- [ps]
  (new-regex-cat ps nil nil []))

(s/fdef new-regex-cat :args (s/cat :ps (s/nilable (s/coll-of any?)) :ks (s/nilable (s/coll-of keyword?)) :fs (s/nilable coll?) :ret :cat/ret) :ret ::spect)
(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
  (if (and ps
           (every? #(conformy? %) ps)
           (every? identity ps))
    (if (accept? p0)
      (let [ret-old ret
            _ (assert ret)
            ret (conj ret (:ret p0))]
        (if pr
          (p/map->RegexCat {:ps pr
                            :ks kr
                            :forms fr
                            :ret ret})
          (accept ret)))
      (p/map->RegexCat {:ps ps
                        :ks ks
                        :forms forms
                        :ret ret}))
    reject))

(extend-type RegexCat
  p/Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  p/Regex
  (derivative [{:keys [ps ks forms ret] :as this} x]
    (let [v (let [ps (map parse-spec ps)
                  [p0 & pr] ps
                  [k0 & kr] ks
                  [f0 & fr] forms]
              (assert ret)
              (maybe-alt-
               (new-regex-cat (cons (derivative p0 x) pr) ks forms ret)
               (if (accept-nil? p0)
                 (derivative (new-regex-cat pr kr fr (with-return p0 ret)) x)
                 reject)))]
      v))
  (re-explain* [{:keys [ps ks forms ] :as spec} path via in x]
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
        (p/explain* pred path via in x))))
  (accept-nil? [this]
    (->>
     this
     :ps
     (map parse-spec)
     (every? accept-nil?)))
  (return- [{:keys [ps ks ret] :as this}]
    (p/return- (with-return (some-> ps first parse-spec) ret)))
  (with-return- [{:keys [ret] :as this} r]
    (let [ret (p/return- this)]
      (if (empty? ret)
        r
        (if r
          (conj r ret)
          (conj [] ret)))))
  (regex? [this]
    true)
  (disentangle [this]
    (->> this
         p/elements
         (map disentangle)
         (apply combo/cartesian-product)
         (map cat-)))
  (constructor [this]
    cat-)
  (elements [this]
    (->> this :ps (mapv parse-spec)))
  (fix-length [s n]
    (loop [rets [[]]
           elems (p/elements s)]
      (let [[e & er] elems]
        (if e
          (let [ss (fix-length e n)]
            (recur
             (mapcat (fn [s]
                       (map (fn [ret]
                              (if (cat? s)
                                (vec (concat ret (p/elements s)))
                                (do
                                  (assert (vector? ret))
                                  (conj ret s)))) rets)) ss)
             er))
          (map cat- rets)))))
  p/WillAccept
  (will-accept- [{:keys [ps ks forms ret] :as this}]
    (if (seq ps)
      (let [ps (map parse-spec ps)
            p (first ps)
            wa (if (accept? p)
                 p
                 (will-accept p))
            [p0 & pr] ps
            [k0 & kr] ks
            [f0 & fr] forms]
        (if (and (accept-nil? p) pr)
          (or- [wa (will-accept (new-regex-cat pr kr fr (with-return p0 ret)))])
          wa))
      nil))
  p/FirstRest
  (first- [this]
    (->> this
         :ps
         (map parse-spec)
         (map (fn [p]
                (if (and (first-rest? p) (p/regex? p))
                  (first- p)
                  p)))
         (filter identity)
         first))
  (rest- [this]
    (let [x (will-accept this)]
      (if (and x (conformy? x))
        (let [dx (derivative this x)]
          (assert (or (spect? dx) (nil? dx)))
          (if dx
            (let [dx (assoc dx :ret [])]
              (if (not (accept? dx))
                dx
                nil))
            nil))
        nil)))
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/DependentSpecs
  (dependent-specs- [this]
    #{(class-spec ISeq)}))

(defn seq? [x]
  (instance? RegexSeq x))

(s/def :seq/splice boolean?)

(s/fdef seq- :args (s/cat :s ::spect-like :opts (s/? (s/keys :opt-un [:seq/splice]))) :ret ::spect)
(defn seq- [s & [{:keys [splice]}]]
  (if (conformy? s)
    (p/map->RegexSeq {:ps [s s]
                      :forms nil
                      :ret []
                      :splice splice})
    reject))

(defn new-regex-seq [ps ret splice forms]
  (assert (= 2 (count ps)))
  (let [[p1 p2] ps]
    (if (every? conformy? ps)
      (if (accept? p1)
        (p/map->RegexSeq {:ps [p2 p2]
                          :forms forms
                          :ret ((fnil conj []) ret (:ret p1))
                          :splice splice})
        (p/map->RegexSeq {:ps [p1 p2]
                          :forms forms
                          :ret ret
                          :splice splice}))
      reject)))

(extend-type RegexSeq
  p/Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  p/Regex
  (derivative [this x]
    (let [{:keys [ps ret splice forms]} this
          [p1 p2] ps
          p1 (parse-spec p1)
          p2 (parse-spec p2)]
      (assert p2)
      (maybe-alt- (new-regex-seq [(derivative p1 x) p2] ret splice forms)
                  (when (accept-nil? p1)
                    (new-regex-seq [(derivative p2 x) p2] (with-return p1 ret) splice forms)))))
  (accept-nil? [this]
    true)
  (return- [this]
    (let [[p1 p2] (:ps this)
          p1 (parse-spec p1)]
      (with-return p1 (:ret this))))
  (with-return- [this r]
    (let [{:keys [splice]} this
          ret (p/return- this)]
      (if (empty? ret)
        r
        ((if splice into conj) r ret))))
  (regex? [this]
    true)
  (elements [this]
    (->> this :ps (map parse-spec)))
  (disentangle [this]
    (->> this
         :ps
         first
         parse-spec
         (disentangle)
         (map seq-)))
  (fix-length [this n]
    (loop [ret [[]]
           n n]
      (let [elem (first (p/elements this))]
        (assert (spect? elem))
        (if (pos? n)
          (recur (conj ret (conj (last ret) elem)) (dec n))
          (conj (map cat- ret) (cat- []))))))
  p/FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (let [x (will-accept this)]
      (if (and x (conformy? x))
        (let [ret (derivative this x)]
          (assert (or (spect? ret) (nil? ret)))
          ret)
        nil)))
  p/WillAccept
  (will-accept- [this]
    (let [[p1 p2] (map parse-spec (:ps this))]
      (if (accept-nil? p1)
        (or- [p1 p2])
        p1)))
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'seq?) (pred-spec #'seqable?) (class-spec clojure.lang.ISeq)}))

(defn filter-alt [ps ks forms f]
  (if (or ks forms)
    (let [pks (->> (map vector ps
                        (or (seq ks) (repeat nil))
                        (or (seq forms) (repeat nil)))
                   (filter #(-> % first f)))]
      [(seq (map first pks)) (when ks (seq (map second pks))) (when forms (seq (map #(nth % 2) pks)))])
    [(seq (filter f ps)) ks forms]))

(defn new-regex-alt [ps ks forms]
  (let [i (first (filter invalid? ps))]
    (if (not i)
      (let [[[p1 & pr :as ps] [k1 :as ks] forms] (filter-alt ps ks forms #(and % (not (reject? %))))]
        (if ps
          (let [ret (p/map->RegexAlt {:ps ps :ks ks :forms forms})]
            (if (nil? pr)
              (if k1
                (if (accept? p1)
                  p1
                  ret)
                p1)
              ret))
          reject))
      i)))

(defn alt? [x]
  (instance? RegexAlt x))

(defn alt- [ps]
  (new-regex-alt ps nil nil))

(defn ?- [x]
  (new-regex-alt [x (accept nil)] nil nil))

(extend-type RegexAlt
  p/Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  p/Regex
  (derivative [{:keys [ps ks forms] :as this} x]
    (let [ps (map parse-spec ps)]
      (new-regex-alt (mapv #(derivative % x) ps) ks forms)))

  (empty-regex [{:keys [ps ks forms] :as this}]
    (p/map->RegexAlt {:ps (map p/empty-regex ps)
                      :ks ks
                      :forms forms}))
  (accept-nil? [{:keys [ps ks forms] :as this}]
    (let [ps (map parse-spec ps)]
      (boolean (some accept-nil? ps))))
  (return- [{:keys [ps ks forms] :as this}]
    (let [ps (map parse-spec ps)
          p0 (->> ps
                  (filter accept-nil?)
                  first)
          r (if (nil? p0)
              nil
              (return p0))]
      r))
  (with-return- [this r]
    (let [ret (p/return- this)]
      (if (= ret nil)
        r
        (conj r ret))))
  (constructor [this]
    alt-)
  (elements [this]
    (->> this :ps (map parse-spec)))
  (disentangle [this]
    (->> this
         p/elements
         (map disentangle)
         (apply concat)))
  (fix-length [this n]
    [this])
  (re-explain* [{:keys [ps ks forms] :as spec} path via in x]
    (if (empty? x)
      [{:path path
        :reason "Insufficient input"
        :val ()
        :via via
        :in in}]
      (apply concat
             (map (fn [k form p]
                    (p/explain* p
                                (if k (conj path k) path)
                                via
                                in
                                x))
                  (or (seq ks) (repeat nil))
                  (or (seq forms) (repeat nil))
                  ps))))
  (regex? [this]
    true)
  p/FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (let [x (will-accept this)]
      (if (and x (conformy? x))
        (derivative this x)
        nil)))
  p/WillAccept
  (will-accept- [this]
    (some->> this
             :ps
             (map parse-spec)
             (remove accept?)
             (mapv will-accept)
             ((fn [ps]
                (if (seq ps)
                  (or- ps)
                  nil)))))
  p/Truthyness
  (truthyness [this]
    (let [b (distinct (map p/truthyness (map parse-spec (:ps this))))]
      (if (= 1 (count b))
        (first b)
        :ambiguous))))

(declare new-regex-plus)

(defn get-spec [spec-name]
  (let [s (s/get-spec spec-name)
        cs (parse-spec s)]
    (if-let [t (data/get-invoke-transformer spec-name)]
      (assoc cs :transformer t)
      cs)))

(declare can-parse?)

(defn form? [x]
  (and (core/seq? x) (symbol? (first x))))

(defn macro? [v]
  (and (var? v) (.isMacro ^Var v)))

(defn known-form? [x]
  (let [sym (first x)
        v (resolve sym)]
    (and (core/seq? x) (symbol? (first x)) (var? v) (can-parse? sym))))

(defn parse-spec*-dispatch [x]
  {:post [(do (when (nil? %)
                (println "don't know how to parse" x)) true)
          %]}
  (cond
    (s/spec? x) :spec
    (s/regex? x) (::s/op x)
    (spect? x) :literal
    (and (form? x) (known-form? x)) (first x)
    (and (form? x) (not (known-form? x)) (macro? (resolve (first x)))) :macro
    (symbol? x) :sym
    (var? x) :var
    (fn-literal? x) :fn-literal
    (keyword? x) :keyword
    (set? x) :set
    (coll? x) :coll
    (class? x) :class
    :else :literal))

(defmulti parse-spec* #'parse-spec*-dispatch)

(defn can-parse? [x]
  (contains? (set (multimethod-dispatch-values parse-spec*)) x))

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

(defn parse-spec- [x]
  {:post [%]}
  (try
    (cond
      (spect? x) x
      (and (symbol? x) (maybe-resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
      (var? x) (parse-spec* (s/spec-impl (var-name x) x nil nil))
      (= ::s/nil x) (accept nil)
      (s/spec? x) (parse-spec* (s/form x))
      (s/regex? x) (parse-spec* x)
      :else (parse-spec* x))
    (catch IllegalArgumentException e
      (println "don't know how to parse:" x)
      (throw e))))

(def parse-spec (memo/memo parse-spec-))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defmethod parse-spec* :keyword [x]
  (if (and (qualified-keyword? x) (s/get-spec x))
    (parse-spec (s/get-spec x))
    (value x)))

(extend-type SpecSpec
  p/Spect
  (conform* [this x]
    (p/conform* (parse-spec (:s this)) x))
  p/WillAccept
  (will-accept- [this]
    (parse-spec (:s this)))
  p/Regex
  (derivative [this x]
    (derivative (parse-spec (:s this)) x))
  (empty-regex [this]
    (p/empty-regex (parse-spec (:s this))))
  (accept-nil? [this]
    (accept-nil? (parse-spec (:s this))))
  (return- [this]
    this)
  (with-return- [this ret]
    (p/with-return- (:s this) ret))
  (regex? [this]
    (-> this :s parse-spec p/regex?))
  (elements [this]
    (-> this :s parse-spec p/elements))
  p/FirstRest
  (first- [this]
    (-> this :s parse-spec first-))
  (rest- [this]
    (-> this :s parse-spec rest-))
  p/Truthyness
  (truthyness [this]
    (-> this :s parse-spec p/truthyness))
  p/Invoke
  (invoke- [this args]
    (-> this :s parse-spec (invoke args)))
  (invoke-accept- [this]
    (-> this :s parse-spec invoke-accept))
  p/DependentSpecs
  (dependent-specs- [this]
    (-> this :s parse-spec dependent-specs))
  p/SpecToClasses
  (spec->classes- [this]
    (-> this :s parse-spec spec->classes)))

(defn spec-spec? [x]
  (instance? SpecSpec x))

(defn spec-spec [s]
  (if (not (spec-spec? s))
    (p/map->SpecSpec {:s s})
    s))

(extend-type DelaySpec
  p/Spect
  (conform* [this x]
    (-> this :s deref (p/conform* x)))
  p/WillAccept
  (will-accept- [this]
    (-> this :s deref p/will-accept-))
  p/Regex
  (derivative [this x]
    (-> this :s deref (derivative x)))
  (empty-regex [this]
    (-> this :s deref p/empty-regex))
  (accept-nil? [this]
    (-> this :s deref accept-nil?))
  (return- [this]
    this)
  (with-return- [this ret]
    (-> this :s deref (p/with-return- ret)))
  (regex? [this]
    (-> this :s deref p/regex?))
  (elements [this]
    (-> this :s deref p/elements))
  p/FirstRest
  (first- [this]
    (-> this :s deref first-))
  (rest- [this]
    (-> this :s deref rest-))
  p/Truthyness
  (truthyness [this]
    (-> this :s deref p/truthyness))
  p/Invoke
  (invoke- [this args]
    (-> this :s deref (invoke args)))
  (invoke-accept- [this]
    (-> this :s deref invoke-accept))
  p/DependentSpecs
  (dependent-specs- [this]
    (-> this :s deref dependent-specs))
  p/SpecToClasses
  (spec->classes- [this]
    (-> this :s deref spec->classes)))

(defn delay-spec? [x]
  (instance? DelaySpec x))

(defmacro delay-spec [s]
  `(p/map->DelaySpec {:s (delay ~s)}))

(extend-regex PredSpec)

(s/def ::pred (s/or :v var? :fn fn? :nil nil?))

(s/fdef pred-spec :args (s/cat :p ::pred) :ret ::spect)
(defn pred-spec [p]
  (p/map->PredSpec {:pred p
                    :form (when (var? p)
                            (var-name p))}))

(predicate-spec pred-spec?)
(defn pred-spec? [x]
  (instance? spectrum.protocols.PredSpec x))

(defn resolve-pred-spec
  "If spec is a PredSpec, find and parse its fnspec"
  [s]
  (if (pred-spec? s)
    (let [fnspec (s/get-spec (:pred s))]
      (if fnspec
        (let [fnspec (parse-spec fnspec)]
          (if (var? (:pred s))
            (assoc fnspec :var (:pred s))
            fnspec))
        (unknown {:message (format "no spec for %s used as pred-spec" (print-str s))})))
    s))

(def any?-form '(clojure.core/fn [x] true))
(def any?-macroexpanded '(fn* ([x] true)))

(s/fdef any-spec? :args (s/cat :s pred-spec?) :ret boolean?)
(defn any-spec?
  "To prevent infinite recursion, recognize if this is the 'any? spec, and return true"
  [pred-spec]
  (or (-> pred-spec :pred (= #'any?))
      (-> pred-spec :pred (= any?-form))
      (-> pred-spec :pred (= any?-macroexpanded))))

(defn object-spec? [x]
  (and (class-spec? x) (= Object (:cls x))))

(defn nil-spec? [x]
  (and (value? x) (= nil (:v x))))

(defn maybe-class [x]
  (cond
    (class-spec? x) (:cls x)
    (class? x) x
    (and (value? x) (class? (:v x))) (:v x)
    :else nil))

(defn default-spec->classes [spec]
  (->>
   (recursive-dependent-specs spec)
   (filter (fn [s]
             (or (class-spec? s)
                 (and (or? s)
                      (every? (fn [p]
                                (class-spec? p)) (:ps s))))))
   (most-specific-spec)
   ((fn [s]
      (if (or? s)
        (->> s
             (p/elements)
             (map (fn [cs]
                    (assert (class-spec? cs))
                    (:cls cs)))
             (set))
        #{(maybe-class s)})))))

(defn standard-spec->classes [s]
  (extend s p/SpecToClasses {:spec->classes- default-spec->classes}))

(defn pred-keyword-invoke [s args]
  (pred-spec #'any?))

(extend-type PredSpec
  p/Spect
  (conform* [spec x]
    (let [pred (:pred spec)]
      (cond
        (any-spec? spec) x
        (and (pred-spec? x) (= pred (:pred x))) x
        (and (= #'class? pred) (class-spec? x)) x

        ;; calling the pred should always be last resort
        ;; TODO remove this, or restrict to only using w/ pure functions. Not technically 'static' analysis.
        ;; (and (conform-pred-args? spec (cat- [x])) (valuey? x)) (do
        ;;                                                          (when (pred (get-value x))
        ;;                                                            x))
        )))
  (explain* [spec path via in x]
    (when (not (valid? spec x))
      [{:path path :pred (:form spec) :val x :via via :in in}]))
  p/WillAccept
  (will-accept- [this]
    this)
  p/Truthyness
  (truthyness [this]
    (condp = (:pred this)
      #'boolean? :ambiguous
      #'false? :falsey
      #'nil? :falsey
      #'any? :ambiguous
      :truthy))
  p/Invoke
  (invoke- [this args]
    (let [pred (:pred this)]
      (cond
        (or (= #'keyword? pred) (= #'symbol? pred)) (pred-keyword-invoke this args)
        (or (= #'ifn? pred) (= #'fn? pred)) (pred-spec #'any?)
        :else (invalid {:message (format "FnSpec: can't invoke %s" (print-str this))}))))
  (invoke-accept- [this]
    (let [pred (:pred this)]
      (cond
        (or (= #'keyword? pred) (= #'symbol? pred)) (cat- [(pred-spec #'any?) (?- (pred-spec #'any?))])
        (= #'ifn? pred) (pred-spec #'any?)
        :else (invalid {:message (format "FnSpec: can't invoke-accept %s" (print-str this))}))))
  p/FirstRest
  (first- [this]
    (let [p (:pred this)]
      (condp = p
        #'nil? (value nil)
        #'seqable? (pred-spec #'any?)
        #'seq? (pred-spec #'any?)
        reject)))
  (rest- [this]
    (let [p (:pred this)]
      (condp = p
        #'nil? (value nil)
        #'seqable? (seq- (pred-spec #'any?))
        #'seq? (seq- (pred-spec #'any?))
        reject))))

(defn maybe-map-equivalence-hack [c]
 ;;; hack for the godawful clojure.lang.MapEquivalence
;;; hack. deftype checks for MapEquivalence, an interface that is
;;; only implemented by APersistentMap, even though the defrecord
;;; constructor takes IPersistentMap.
  (if (= clojure.lang.MapEquivalence c)
    clojure.lang.APersistentMap
    c))

(s/fdef class-spec :args (s/cat :c class?) :ret ::spect)
(defn class-spec [c]
  (assert (class? c) (format "not class?: %s %s" c (class c)))
  (p/map->ClassSpec {:cls c}))

(predicate-spec class-spec?)
(defn class-spec? [x]
  (instance? ClassSpec x))

(defn isa-boxed? [child parent]
  (or (isa? child parent)
      (and child parent (isa? (j/maybe-box child) (j/maybe-box parent)))))

(predicate-spec spec->classes?)
(defn spec->classes? [x]
  (satisfies? p/SpecToClasses x))

(s/def ::spec->classes (s/or :s class? :or-s (s/coll-of class? :kind set?)))
(s/fdef spec->classes :args (s/cat :s ::spect) :ret ::spec->classes)
(defn spec->classes
  "Given a spec, return the set of concrete classes this spec could be.

   Because specs are more precise than class checks, casting to a
   class can destroy information. Using this anywhere other than java
   interop is a code smell."
  [spec]
  {:post [(do (when-not (s/valid? ::spec->classes %)
                (println "spec->classes" spec "=>" %)) true)
          (validate! ::spec->classes %)]}
  (if (spec->classes? spec)
    (p/spec->classes- spec)
    (default-spec->classes spec)))

(extend-type ClassSpec
  p/Spect
  (conform* [this v]
    (let [{:keys [cls]} this
          v-classes (spec->classes v)]
      (or
       (when (= Object cls)
         v)
       (when (some (fn [c] (isa? c cls)) v-classes)
         v)
       (when (some (fn [vc]
                     (j/castable? cls vc)) v-classes)
         v))))
  p/WillAccept
  (will-accept- [this]
    this)
  p/Truthyness
  (truthyness [this]
    (condp = (:cls this)
      Boolean :ambiguous
      Boolean/TYPE :ambiguous
      Object :ambiguous
      nil :falsey
      :truthy))
  p/DependentSpecs
  (dependent-specs- [this]
    (let [{:keys [cls]} this
          ret (if (= clojure.lang.MapEquivalence cls)
                #{(class-spec clojure.lang.APersistentMap)}
                #{})
          ret (if (j/primitive? cls)
                (set/union (dependent-specs (class-spec (j/primitive->class cls))))
                ret)
          ret (apply set/union ret (map (comp dependent-specs class-spec) (ancestors cls)))]
      ret))
  p/SpecToClasses
  (spec->classes- [this]
    (set [(:cls this)])))

(extend-regex ClassSpec)
(first-rest-singular ClassSpec)

(defn protocol-spec? [x]
  (instance? ProtocolSpec x))

(extend-type ProtocolSpec
  p/Spect
  (conform* [this x]
    (cond
      (protocol-spec? x) (when (= (:p x) (:p this))
                           x)
      (value? x) (when (satisfies? (:p this) (:v x))
                   x)))
  p/WillAccept
  (will-accept- [this]
    this))

(extend-regex ProtocolSpec)

(s/fdef protocol- :args (s/cat :p protocol?) :ret ::spect)
(defn protocol- [p]
  (p/map->ProtocolSpec {:p p}))

(defmethod parse-spec* :macro [x]
  (let [v (resolve (first x))
        args (rest x)
        form (apply v nil nil args)]
    (parse-spec* form)))

(defmethod parse-spec* :sym [x]
  (let [v (resolve x)]
    (if v
      (cond
        (var? v) (p/map->PredSpec {:pred v
                                   :form (symbol (str (.ns ^Var v)) (str (.sym ^Var v)))})
        (class? v) (p/map->ClassSpec {:cls v})
        :else (assert false (format "unknown: %s" x)))
      (value x))))

(defmethod parse-spec* :fn-literal [x]
  (p/map->PredSpec {:pred (eval x)
                    :form x}))

(defmethod parse-spec* 'clojure.core/fn [x]
  (if (= x any?-form)
    (pred-spec #'any?)
    (do
      (p/map->PredSpec {:pred nil ;;(eval x)
                        :form x}))))

(defmethod parse-spec* 'fn* [x]
  (if (= x any?-form)
    (pred-spec #'any?)
    (do
      (p/map->PredSpec {:pred nil ;;(eval x)
                        :form x}))))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (second x)))

(defmethod parse-spec* 'var [x]
  (parse-spec* (second x)))

(defmethod parse-spec* `s/spec [x]
  (spec-spec (parse-spec* (second x))))

(defn unquote-form
  "Given a '(quote foo), return 'foo"
  [f]
  (first (rest f)))

(defmethod parse-spec* `s/spec-impl [x]
  (let [[form pred & _ ] (rest x)]
    (spec-spec (unquote-form form))))

(defmethod parse-spec* ::s/pcat [x]
  (p/map->RegexCat {:ks (:ks x)
                    :ps (mapv (fn [[form pred]]
                                (if (::s/op pred)
                                  pred
                                  form)) (map vector (:forms x) (:ps x)))
                    :forms (:forms x)
                    :ret []}))

(defmethod parse-spec* ::s/accept [x]
  (accept (if (= (:ret x) ::s/nil)
            (value nil)
            (:ret x))))

(defmethod parse-spec* `s/cat [x]
  (let [pairs (->> x rest (partition 2))
        ks (map first pairs)
        ps (map second pairs)]
    (p/map->RegexCat {:ks ks
                      :ps ps
                      :forms ps
                      :ret []})))

(defmethod parse-spec* `s/cat-impl [x]
  (let [[ks ps forms] (rest x)
        forms (unquote-form forms)]
    (p/map->RegexCat {:ks ks
                      :ps forms
                      :ret []})))

(defmethod parse-spec* ::s/rep [x]
  (let [forms (if (vector? (:forms x))
                (:forms x)
                [(:forms x)])]
    (assert (= 1 (count forms)))
    (seq- (first forms) {:splice (:splice x)})))

(defmethod parse-spec* `s/rep-impl [x]
  (let [[form pred] (rest x)
        form (unquote-form form)]
    (seq- form {:splice false})))

(defmethod parse-spec* `s/+ [x]
  (let [forms (rest x)
        p (first forms)
        p (parse-spec p)]
    (assert (= 1 (count forms)))
    (p/map->RegexCat {:forms forms
                      :ps [p (seq- p {:splice true})]
                      :ret []})))

(defmethod parse-spec* `s/rep+impl [x]
  (let [[form pred] (rest x)
        form (unquote-form form)]
    (p/map->RegexCat {:forms [form]
                      :ps [form (seq- form {:splice true})]
                      :ret []})))

(defmethod parse-spec* `s/* [x]
  (let [forms (rest x)
        form (first forms)]
    (assert (= 1 (count forms)))
    (seq- form)))

(defmethod parse-spec* ::s/alt [x]
  (let [pairs (map vector (:ps x) (:forms x))]
    (p/map->RegexAlt {:ks (:ks x)
                      :forms (:forms x)
                      :ps (:forms x)})))

(defmethod parse-spec* `s/? [x]
  (p/map->RegexAlt {:ps [(second x) (accept nil)]}))

(defmethod parse-spec* `s/alt [x]
  (let [pairs (partition 2 (rest x))
        ks (mapv first pairs)
        forms (mapv second pairs)]
    (p/map->RegexAlt {:ks ks
                      :forms forms
                      :ps forms})))

(defmethod parse-spec* `s/alt-impl [x]
  (let [[ks ps forms] (rest x)]
    (p/map->RegexAlt {:ks ks
                      :forms forms
                      :ps (unquote-form forms)})))

(defmethod parse-spec* `s/maybe-impl [x]
  (let [[pred form] (rest x)
        form (unquote-form form)]
    (p/map->RegexAlt {:ps [form (accept nil)]})))

(defmethod parse-spec* :clojure.spec.alpha/amp [x]
  (unknown {:message (format "TODO don't know how to handle %s" x)}))

(defmethod parse-spec* `s/amp-impl [x]
  (unknown {:message (format "TODO don't know how to handle %s" x)}))

(defn not? [x]
  (instance? NotSpec x))

(s/fdef not- :args (s/cat :s ::spect) :ret ::spect)
(defn not- [s]
  (cond
    (not? s) (-> s :s)
    (value? s) (value (not (:v s)))
    :else (p/map->NotSpec {:s s})))

(extend-type NotSpec
  p/Spect
  (conform* [this x]
    (when (and (not (valid? (parse-spec (:s this)) x))
               (not (valid? x (parse-spec (:s this)))))
      x))
  p/WillAccept
  (will-accept- [this]
    this)
  p/Truthyness
  (truthyness [this]
    (let [t (p/truthyness (:s this))]
      (condp = t
        :ambiguous :ambiguous
        :truthy :falsey
        :falsey :truthy))))

(extend-regex NotSpec)
(first-rest-singular NotSpec)

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:ps and-s))
    x))

(predicate-spec and?)
(defn and? [x]
  (instance? spectrum.protocols.AndSpec x))

(s/fdef and-classes-compatible? :args (s/cat :ps (s/coll-of ::spect-like)) :ret boolean?)
(defn and-classes-compatible?
  "True if the `and` pred java classes are incompatible (concrete classes that aren't ancestors)"
  [ps]
  (let [compatible? (fn [a b]
                      {:pre [(class? a) (class? b)]}
                      (and ;; (not (= Object a))
                       (or (isa? a b)
                           (isa? b a)
                           (j/castable? a b)
                           (and (j/interface? a) (j/subclassable? b))
                           (and (j/interface? b) (j/subclassable? a)))))
        ps (map parse-spec ps)
        ps-classes (map (fn [p]
                          (spec->classes p)) ps)]
    (loop [[p-classes & pr-classes] ps-classes]
      (if p-classes
        (if (every? (fn [prs]
                      (some (fn [p]
                              (some (fn [pr]
                                      (compatible? p pr)) prs)) p-classes)) pr-classes)
          (recur pr-classes)
          false)
        true))))

(defn and-not-contradiction?
  "True if ps contains x and (not- x)"
  [ps]
  (let [nots (filter not? ps)
        not-preds (set (map :s nots))]
    (some (fn [p]
            (some (fn [np]
                    (valid? np p)) not-preds)) ps)))

(defn and-value-contradiction?
  "true if `and` ps contains two non-equal values, or values that don't conform to other constraints"
  [ps]
  (let [{values true non-values false} (group-by value? ps)]
    (if (seq values)
      (or (not (apply = (map :v values)))
          (not (every? (fn [v]
                         (every? (fn [s]
                                   (valid? s v)) non-values)) values)))
      false)))

(s/fdef and-consolidate :args (s/cat :ps (s/coll-of ::spect)) :ret (s/coll-of ::spect))
(defn and-consolidate
  "Given the :ps for an `and`, simplify and consolidate forms"
  [ps]
  {:post [(validate! (s/coll-of ::spect-like) %)]}
  (let [ps-orig ps
        ps (distinct ps)
        ps (map maybe-convert-value ps)
        {ands true not-ands false} (group-by and? ps)
        {fns true not-fns false} (group-by fn-spec? ps)
        ps (if (seq fns)
             (conj not-ands (merge-fn-specs fns))
             ps)
        ps (concat (seq not-ands) (distinct (mapcat (fn [a] (:ps a)) ands)))
        {ors true not-ors false} (group-by or? ps)
        ors (mapcat (fn [o] (:ps o)) ors)
        ps (filter identity (concat (seq not-ors) [(when (seq ors)
                                                     (or- ors))]))
        ps (distinct ps)
        ps (remove any-spec? ps)]
    ps))

(s/fdef and- :args (s/cat :forms (s/coll-of ::spect-like :gen-max 5)) :ret ::spect)
(defn and- [ps]
  (let [ps (and-consolidate ps)]
    (cond
      (>= (count ps) 2) (p/map->AndSpec {:ps ps})
      :else (first ps))))

(s/fdef and-conj :args (s/cat :s ::spect :x ::spect) :ret ::spect)
(defn and-conj
  [s x]
  (and- (conj (:ps s) x)))

(defn and-not
  "Adds (and s (not x)), removing x from an or-pred if present"
  [s x]
  (cond
    (value? s) s ;; adding not to a value doesn't make it more specific
    (and? s) (and-conj s (not- x))
    :else (and- [(maybe-or-disj s x) (not- x)])))

(defn equivalent? [s1 s2]
  (and (valid? s1 s2)
       (valid? s2 s1)))

(s/fdef add-constraint :args (s/cat :a ::spect :b ::spect) :ret ::spect)
(defn add-constraint
  "Given a spec s, update it to also conform to spec `constraint`"
  [s constraint]
  {:pre [(do (when-not (spect? s) (println "add constraint:" s constraint)) true) (spect? s) (spect? constraint)]
   :post [(spect? %)]}
  (cond
    (value? s) (if (valid? constraint s)
                 s ;; can't make values more specific
                 (invalid {:message (format "can't add constraint %s to %s" (print-str constraint) (print-str s))}))

    (any-spec? constraint) s
    (object-spec? constraint) s

    (any-spec? s) constraint
    (object-spec? s) constraint

    (and? s) (and-conj s constraint)
    :else (and- [s constraint])))

(s/fdef add-or-constraint :args (s/cat :s ::spect :constraint ::spect) :ret ::spect)
(defn add-or-constraint
  "given a spec s, `or` it with constraint"
  [s constraint]
  (or- [s constraint]))

(s/fdef non-contradiction? :args (s/cat :s ::spect :constraint ::spect) :ret boolean?)
(defn non-contradiction?
  "True if adding constraint to s won't result in contradiction"
  [s constraint]
  (let [s* (add-constraint s constraint)
        {:keys [ps]} s*]
    (cond
      (and? s*) (and (conformy? s*)
                     (and-classes-compatible? ps)
                     (not (and-not-contradiction? ps))
                     (not (and-value-contradiction? ps)))
      :else (conformy? s*))))

(defn or-or-invalid
  [ps message]
  (if (seq ps)
    (or- ps)
    (invalid {:message message})))

(extend-type AndSpec
  p/Spect
  (conform* [this x]
    (conform this x))
  p/DependentSpecs
  (dependent-specs- [spec]
    (->> spec
         :ps
         (map parse-spec)
         (map dependent-specs)
         (apply set/union)))
  p/WillAccept
  (will-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (and-)))
  p/Truthyness
  (truthyness [this]
    (let [b (distinct (->> this :ps (map parse-spec)  (map p/truthyness)))]
      (if (= 1 (count b))
        (first b)
        :ambiguous)))
  p/FirstRest
  (first- [this]
    (->> this
         :ps
         (map parse-spec)
         (filter first-rest?)
         (map first-)
         (filter identity)
         (remove (fn [s]
                   (or (unknown? s)
                       (reject? s)
                       (invalid? s))))
         first))
  (rest- [this]
    (->> this
         :ps
         (map parse-spec)
         (filter first-rest?)
         (map rest-)
         (filter identity)
         (remove (fn [s]
                   (or (unknown? s)
                       (reject? s)
                       (invalid? s))))
         first))
  p/KeysGet
  (keys-get- [this k]
    (->> this
         :ps
         (map parse-spec)
         (map (fn [p]
                (keys-get p k)))
         (filter identity)
         (first)))
  p/Invoke
  (invoke- [this args]
    (->> this
         :ps
         (map parse-spec)
         (filter invoke?)
         (map (fn [p]
                (invoke p args)))
         (filter conformy?)
         (#(or-or-invalid % (format "and-: Can't invoke %s with %s" (print-str this) (print-str args))))))
  (invoke-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (map invoke-accept)
         (filter conformy?)
         (#(or-or-invalid % (format "and-: Can't invoke accept %s" (print-str this))))))
  p/Regex
  (regex? [this]
    (->> this
         :ps
         (map parse-spec)
         (some p/regex?)))
  (derivative [this x]
    (let [resp (conform this x)]
      (if (conformy? resp)
        (accept resp)
        (->> this
             :ps
             (map parse-spec)
             (map (fn [p]
                    (derivative p x)))
             (filter conformy?)
             ((fn [ps]
                (if (seq ps)
                  (and- ps)
                  reject)))))))
  (disentangle [this]
    (->> this
         :ps
         (map parse-spec)
         (map disentangle)
         (apply combo/cartesian-product)
         (map and-)))
  (fix-length [this n]
    (->> this
         :ps
         (map parse-spec)
         (map #(fix-length % n))
         (apply combo/cartesian-product)
         (map and-)))
  (accept-nil? [this]
    (->> this
         :ps
         (map parse-spec)
         (some accept-nil?)
         (boolean)))
  (elements [this]
    (->> this
         :ps
         (map parse-spec)
         (filter p/regex?)
         (map p/elements)
         ((fn [se]
            (println "se:" se (count se))
            (assert (< (count se) 2))
            se))
         (first)))
  (return- [this]
    this)
  (with-return- [this x]
    (->> this
         :ps
         (map parse-spec)
         (mapcat (fn [p]
                   (with-return p x)))
         ((fn [ps]
            (if (seq ps)
              (and- ps)
              x))))))

(defmethod parse-spec* `s/and [x]
  (and- (rest x)))

(defmethod parse-spec* `s/and-spec-impl [x]
  (let [[forms preds gen-fn] (rest x)
        ps (unquote-form forms)]
    (and- ps)))

(predicate-spec or?)
(defn or? [x]
  (instance? spectrum.protocols.OrSpec x))

(s/def :or/ps (s/coll-of ::spect-like))

(s/fdef map->OrSpec :args (s/cat :m (s/keys :req-un [:or/ps])) :ret or?)

(defn or-consolidate
  "Given the ps for an `or`, simplify and consolidate terms"
  [ps]
  (let [or-ps (mapcat (fn [p] (when (or? p)
                                (:ps p))) ps)
        ps (remove or? ps)
        ps (remove bottom? ps)
        ps (concat ps or-ps)
        ps (map (fn [p]
                  (if (object-spec? p)
                    (pred-spec #'any?)
                    p)) ps)

        ;; if there's an any?, We could replace all predicates with
        ;; any? here, but that's not as helpful for the user.

        ps (if (some any-spec? ps)
             (conj (remove any-spec? ps) (first (filter any-spec? ps)))
             ps)
        ps (set ps)]
    ps))

(s/def ::or-args (s/coll-of (s/nilable ::spect-like) :gen-max 5))
(s/def ::or-ret (s/nilable ::spect))
(s/fdef or- :args (s/cat :ps ::or-args) :ret ::or-ret)
(defn or- [ps]
  {:pre [(validate! ::or-args ps)]
   :post [(validate! ::or-ret %)]}
  (let [ps (or-consolidate ps)]
    (cond
      (some invalid? ps) (do (invalid {:message "or invalid"
                                       :causes (filter invalid? ps)}))
      (some reject? ps) reject
      (>= (count ps) 2) (p/map->OrSpec {:ps ps})
      (= 1 (count ps)) (first ps)
      :else (bottom {:message "or- with no arguments"}))))

(s/fdef or-conj :args (s/cat :s ::spect :x ::spect) :ret ::spect)
(defn or-conj [s x]
  (if (or? x)
    (or- (conj (:ps s) x))
    (or- [s x])))

(extend-type OrSpec
  p/Spect
  (conform* [this x]
    (->>
     (:ps this)
     (map parse-spec)
     (some (fn [p]
             (when (valid? p x)
               x)))))
  (disentangle [this]
    (->> this
         p/elements
         (mapcat disentangle)))
  p/DependentSpecs
  (dependent-specs- [this]
    (->> (:ps this)
         (map parse-spec)
         (map dependent-specs)
         (apply set/intersection)))
  p/WillAccept
  (will-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (remove accept?)
         (mapv will-accept)
         (or-)))
  p/Truthyness
  (truthyness [this]
    (let [b (->> this :ps (map parse-spec) (map p/truthyness) distinct)]
      (if (= 1 (count b))
        (first b)
        :ambiguous)))
  p/FirstRest
  (first- [this]
    (->> this
         :ps
         (map parse-spec)
         (map first-)
         (or-)))
  (rest- [this]
    (->> this
         :ps
         (map parse-spec)
         (map rest-)
         (or-)))
  p/Invoke
  (invoke- [this args]
    (->> this
         :ps
         (map parse-spec)
         (map (fn [p]
                (invoke p args)))
         (filter conformy?)
         (#(or-or-invalid % (format "or-: Can't invoke %s" (print-str this))))))
  (invoke-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (map invoke-accept)
         (filter conformy?)
         (#(or-or-invalid % (format "or-: Can't invoke-accept %s" (print-str this))))))
  p/KeywordInvoke
  (keyword-invoke- [this args]
    (->> (:ps this)
         (map parse-spec)
         (filter keyword-invoke?)
         (map (fn [p]
                (keyword-invoke p args)))
         (distinct)
         ((fn [ps]
            (if (seq ps)
              (or- ps)
              (unknown {:message (format "keyword invoke %s %s" (print-str this) (print-str args))}))))))
  p/KeysGet
  (keys-get- [this k]
    (->> this
         :ps
         (mapv parse-spec)
         (mapv (fn [p] (keys-get p k)))
         (distinct)
         (or-)))
  p/Regex
  (regex? [this]
    (->> this
         :ps
         (map parse-spec)
         (some p/regex?)))
  (derivative [this x]
    (let [resp (conform this x)]
      (if (conformy? resp)
        (accept resp)
        (->> this
             :ps
             (map parse-spec)
             (map (fn [p]
                    (derivative p x)))
             (filter conformy?)
             ((fn [ps]
                (if (seq ps)
                  (or- ps)
                  reject)))))))
  (accept-nil? [this]
    (->> this
         :ps
         (map parse-spec)
         (some accept-nil?)
         (boolean)))
  (elements [this]
    (->> this
         :ps
         (map parse-spec)))
  (fix-length [this n]
    (->> this
         :ps
         (map parse-spec)
         (map #(fix-length % n))
         (apply concat)))
  (disentangle [this]
    (->> this
         :ps
         (map parse-spec)
         (mapcat disentangle)))
  (return- [this]
    this)
  (with-return- [this x]
    (->> this
         :ps
         (map parse-spec)
         (mapcat (fn [p]
                   (with-return p x)))
         ((fn [ps]
            (if (s/valid? (s/coll-of ::spect) ps)
              (or- ps)
              x)))))
  p/SpecToClasses
  (spec->classes- [this]
    (->> this
         :ps
         (map parse-spec)
         (map spec->classes)
         (apply set/union))))

(defn or-some
  "clojure.core/some, called on each pred in the orspec"
  [f or-spec]
  (some f (->> or-spec :ps (map parse-spec))))

(s/fdef or-disj :args (s/cat :s or? :p ::spect) :ret ::spect)
(defn or-disj
  "Remove pred from the set of preds"
  [s pred]
  (->> s
       :ps
       (map parse-spec)
       (map (fn [p]
              (maybe-or-disj p pred)))
       (filter (fn [p]
                 (not (equivalent? p pred))))
       (or-)))

(defn maybe-or-disj
  "If s is an `or`, disj pred from it, else s"
  [s pred]
  (if (or? s)
    (or-disj s pred)
    s))

(defn or-every?
  "true if f applied with each element of the or-spec and args is truthy"
  [f or & args]
  (every? (fn [p]
            (apply f p args)) (:ps or)))

(defmethod parse-spec* `s/or [x]
  (let [pairs (map vec (partition 2 (rest x)))
        ks (map first pairs)
        ps (map second pairs)]
    (or- ps)))

(defmethod parse-spec* `s/or-spec-impl [x]
  (let [[ks forms ps gen-fn] (rest x)
        forms (unquote-form forms)]
    (or- forms)))


(defn tuple-spec [ps]
  (p/map->TupleSpec {:ps ps}))

(extend-type TupleSpec
  p/Spect
  (conform* [spec xs]
    (let [xs-orig xs]
      (loop [ps (:ps spec)
             xs xs]
        (let [p (first ps)
              x (first- xs)]
          (cond
            (and p x) (when (valid? (parse-spec p) (parse-spec x))
                        (recur (rest ps) (rest- xs)))
            (and (not p) (not x)) xs-orig)))))
  p/Regex
  (accept-nil? [this]
    (not (seq (:ps this))))
  p/FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (when-let [r (-> this :ps rest seq)]
      (tuple-spec r))))

(extend-regex TupleSpec)

(defmethod parse-spec* `s/tuple [x]
  (let [preds (rest x)]
    (p/map->TupleSpec {:ps (vec preds)})))

(defmethod parse-spec* `s/tuple-impl [x]
  (let [[forms preds] (rest x)]
    (p/map->TupleSpec {:ps (unquote-form forms)})))

(defn keyspec-get-key-
  ([s key]
   (some (fn [key-type]
           (when-let [v (get-in s [key-type key])]
             [key-type (parse-spec v)])) [:req :req-un :opt :opt-un])))

(defn keyspec-get-key
  ([s key]
   (let [k (maybe-strip-value key)
         [key-type val] (keyspec-get-key- s k)]
     (if val
       (if (contains? #{:opt :opt-un} key-type)
         (or- [val (value nil)])
         val)
       (value nil))))
  ([s key else]
   (let [k (maybe-strip-value key)
         [key-type val] (keyspec-get-key- s k)]
     (if val
       (if (contains? #{:opt :opt-un} key-type)
         (or- [val else])
         val)
       else))))

(predicate-spec keys-spec?)
(defn keys-spec? [x]
  (instance? spectrum.protocols.KeysSpec x))

(s/fdef conform-keys-keys :args (s/cat :s ::keys-spec :x ::keys-spec) :ret any?)
(defn conform-keys-keys [this x]
  (when (or
         (= this x) ;; short circuit
         (and
          (keys-spec? x)
          ;; x keys conform to spec
          (every? (fn [[key spec]]
                    (valid? (parse-spec spec) (parse-spec (get-in x [:req key])))) (:req this))
          (every? (fn [[key spec]]
                    (valid? (parse-spec spec) (parse-spec (get-in x [:req-un (strip-namespace key)])))) (:req-un this))))
    x))

(defn conform-keys-value [s x]
  (let [x* (get-value x)]
    (when (and
           ;; x keys conform to spec
           (every? (fn [[key spec]]
                     (valid? (parse-spec spec) (parse-spec (get x* key)))) (:req s))
           (every? (fn [[key spec]]
                     (valid? (parse-spec spec) (parse-spec (get x* (strip-namespace key))))) (:req-un s))
           (every? (fn [[key spec]]
                     (if-let [v (parse-spec (get x* key))]
                       (valid? (parse-spec spec) v)
                       true)) (:opt s))
           (every? (fn [[key spec]]
                     (if-let [v (get x* (strip-namespace key))]
                       (valid? (parse-spec spec) (parse-spec v))
                       true)) (:req-un s)))
      x)))

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
               (p/explain* spec (conj path key) via in val)))))))

(s/def ::keys-spec keys-spec?)

(s/fdef keys-spec :args (s/cat :req (s/nilable (s/map-of qualified-keyword? ::spect-like))
                               :req-un (s/nilable (s/map-of keyword? ::spect-like))
                               :opt (s/nilable (s/map-of qualified-keyword? ::spect-like))
                               :opt-un (s/nilable (s/map-of keyword? ::spect-like)))
        :ret keys-spec?)

(defn keys-spec [req req-un opt opt-un]
  (p/map->KeysSpec {:req req
                    :req-un (into {} (map (fn [[k s]]
                                            [(strip-namespace k) s]) req-un))
                    :opt opt
                    :opt-un (into {} (map (fn [[k s]]
                                            [(strip-namespace k) s]) opt-un))}))

(defn keys-invoke [spec args]
  (let [k (first- args)
        else (second- args)
        rest (rest- (rest- args))]
    (cond
      rest (invalid {:message (format "keys invoke: too many args:" (print-str spec) (print-str args))})
      else (keyspec-get-key spec k else)
      k (keyspec-get-key spec k)
      :else (invalid {:message "not enough args"}))))

(extend-type KeysSpec
  p/WillAccept
  (will-accept- [this]
    this)
  p/DependentSpecs
  (dependent-specs- [this]
    #{(class-spec clojure.lang.PersistentHashMap) (pred-spec #'map?) (pred-spec #'coll?)})
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/KeywordInvoke
  (keyword-invoke- [this args]
    (keys-invoke this args))
  p/Invoke
  (invoke- [this args]
    (keys-invoke this args))
  (invoke-accept- [this]
    (or- [(cat- [(pred-spec #'any?)])
          (cat- [(pred-spec #'any?) (pred-spec #'any?)])]))
  p/KeysGet
  (keys-get- [this k]
    (assert (keyword? k))
    (or
     (some->> [:req :req-un]
              (some (fn [key-type]
                      (get-in this [key-type k])))
              (parse-spec))
     (some->> [:opt :opt-un]
              (some (fn [key-type]
                      (get-in this [key-type k])))
              (parse-spec)
              (#(or- [% (value nil)])))
     (value nil)))
  p/Spect
  (conform* [this x]
    (cond
      (keys-spec? x) (conform-keys-keys this x)
      (value? x) (conform-keys-value this x)))
  (explain* [spec path via in x]
    (explain-keys spec path via in x)))

(extend-regex KeysSpec)

(defn keys-contains?
  "clojure.core/contains? for keys-spec"
  [ks key]
  (some (fn [key-type]
          (contains? (get ks key-type) key)) [:req :req-un :opt :opt-un]))

(extend-regex CollOfSpec)
(will-accept-this CollOfSpec)

(s/fdef coll-of :args (s/cat :s ::spect-like :kind (s/? (s/nilable coll?))) :ret ::spect)
(defn coll-of
  ([s]
   (coll-of s nil))
  ([s kind]
   (p/map->CollOfSpec {:s s
                       :kind kind})))

(predicate-spec coll-of?)
(defn coll-of? [x]
  (instance? spectrum.protocols.CollOfSpec x))

(s/fdef infinite? :args (s/cat :r first-rest?) :ret boolean?)
(defn infinite?
  "True if this spec accepts infinite input"
  [r]
  (or (seq? r)
      (coll-of? r)
      (unknown? r)
      (if-let [n (some-> r :ps first)]
        (recur n)
        false)))

(s/fdef coll-items :args (s/cat :s ::spect) :ret (s/coll-of ::spect :kind set?))
(defn coll-items
  "The set of all items in a regex/coll spec"
  [s]
  {:post [(validate! (s/coll-of ::spect :kind set?) %)]}
  (loop [ret #{}
         s s]
    (let [v (first- s)]
      (if (conformy? v)
        (let [ret (conj ret v)]
          (if (and (not (infinite? s)) (rest- s))
            (recur ret (rest- s))
            ret))
        ret))))

(s/fdef will-accept-concrete :args (s/cat :s ::spect) :ret (s/* ::spect))
(defn will-accept-concrete
  "will-accept, but recursively resolve or/alt specs, returns a seq of spects"
  [s]
  (->> s
       (will-accept)
       ((fn [x]
          (cond
            (or (or? x) (alt? x)) (->> x :ps (map parse-spec) (mapcat will-accept-concrete))
            :else [x])))))

(s/fdef all-possible-values :args (s/cat :r ::spect :n nat-int?) :ret (s/coll-of ::spect))
(defn all-possible-values
  "Given a regex, disentangle and fix length, returning all concrete specs up to length n"
  [spec n]
  (->> spec
       (disentangle)
       (mapcat (fn [s]
                 (fix-length s n)))
       (filter (fn [s]
                 {:pre [(spect? s)]}
                 (if (p/regex? s)
                   (<= (count (p/elements s)) n)
                   [s])))
       (distinct)))

(defn all-possible-values-length-n
  "all-possible-values with length == n, but return a single cat, `or`ing together each element"
  [spec n]
  (if (and (conformy? spec) (known? spec))
    (->> (all-possible-values spec n)
         (filter (fn [s]
                   (= n (count (p/elements s)))))
         (map p/elements)
         ((fn [elements]
            (if (seq elements)
              (cat- (apply mapv (fn [& es]
                                  (or- es)) elements))
              (invalid {:message (format "no possible value of length n")})))))
    spec))

(s/fdef conform-collof-value :args (s/cat :collof ::spect :x (s/nilable value?)))
(defn conform-collof-value [collof x]
  (let [s (parse-spec (:s collof))
        v (get-value x)]
    (when (and (or (nil? (:kind collof))
                   (and (:empty-kind collof)
                        (= (:empty-kind collof)
                           (empty v)))
                   (empty? v))
               (or (and (sequential? v)
                        (not (seq v)))
                   (valid? s x)))
      x)))

(s/fdef coll-of-key :args (s/cat :s ::spect) :ret #{:map :set :vector :unknown})
(defn coll-of-kind
  "Given a coll-of spect, return its kind as a keyword"
  [s]
  (condp = (::s/kind-form s)
    'clojure.core/map? :map
    'clojure.core/set? :set
    'clojure.core/vector? :vector
    :unknown))

(defn coll-of-invoke-dispatch [s args]
  (coll-of-kind s))

(defmulti coll-of-invoke #'coll-of-invoke-dispatch)

(defmethod coll-of-invoke :default [s args]
  (unknown {:message (format "don't know how to invoke %s" (print-str s))}))

(defmethod coll-of-invoke :map [s args]
  (let [key (first- args)
        else (or (second- args) (value nil))
        rest (rest- (rest- args))
        map-key-spec (-> s :s parse-spec first-)
        map-val-spec (-> s :s parse-spec second-)]
    (cond
      rest (invalid {:message (format "too many args to invoke, got %s" (print-str args))})
      (not key) (invalid {:message "not enough args to invoke"})
      (valid? map-key-spec key) (or- [map-val-spec else])
      (or? key) (if (or-some #(valid? map-key-spec %) key)
                  (or- [map-val-spec else])
                  (value nil))
      :else (if else
              else
              (value nil)))))

(extend-type CollOfSpec
  p/Spect
  (conform* [this x]
    (cond
      (instance? spectrum.protocols.CollOfSpec x) (when (valid? (parse-spec (:s this)) (parse-spec (:s x)))
                                                    x)
      (value? x) (conform-collof-value this x)))
  p/FirstRest
  (first- [this]
    (parse-spec (:s this)))
  (rest- [this]
    this)
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/Invoke
  (invoke- [this args]
    (coll-of-invoke this args))
  p/DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'seqable?) (class-spec (or (class (:s this)) clojure.lang.PersistentList))})
  p/SpecToClasses
  (spec->classes- [this]
    #{clojure.lang.IPersistentCollection clojure.lang.ISeq clojure.lang.Seqable}))

(def kind->coll
  {'clojure.core/vector? []
   'clojure.core/sequential? []
   'clojure.core/set? #{}
   'clojure.core/map? {}})

(defn parse-coll-of [x]
  (let [args (rest x)
        s (first args)
        opts (apply hash-map (rest args))
        empty-kind (get kind->coll (get opts :kind))]
    (p/map->CollOfSpec (merge {:s s
                               :empty-kind empty-kind} opts))))

(extend-type ArrayOf
  p/Spect
  (conform* [this x]
    (when (and (instance? spectrum.protocols.ArrayOf x) (valid? (parse-spec (:s this)) (parse-spec (:s x))))
      x))
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/WillAccept
  (will-accept- [this]
    this))

(first-rest-singular ArrayOf)
(extend-regex ArrayOf)

(s/fdef array-of :args (s/cat :x class-spec?) :ret ::spect)
(defn array-of [p]
  (p/map->ArrayOf {:p p}))

(defmethod parse-spec* `s/nilable [x]
  (let [s (second x)]
    (or- [(parse-spec s) (parse-spec #'nil?)])))

(defmethod parse-spec* `s/nilable-impl [x]
  (let [[form pred gen-fn] (rest x)
        form (unquote-form form)]
    (or- [form (pred-spec #'nil?)])))

(defmethod parse-spec* `s/or [x]
  (let [pairs (partition 2 (rest x))
        keys (mapv first pairs)
        forms (mapv second pairs)]
    (or- forms)))

(defmethod parse-spec* `s/keys [x]
  (let [args (->> (rest x)
                  (partition 2)
                  (map (fn [[key-type specs]]
                         [key-type (into {} (map (fn [spec-name]
                                                   (if-let [s (s/get-spec spec-name)]
                                                     [spec-name (s/form s)]
                                                     (throw (Exception. (format "Could not resolve spec: %s" spec-name))))) specs))]))
                  (into {} ))]
    (keys-spec (:req args)
               (:req-un args)
               (:opt args)
               (:opt-un args))))

(defmethod parse-spec* `s/map-spec-impl [x]
  (let [args (first (rest x))]
    (let [parse-keys (fn [ks]
                       (into {} (map (fn [k]
                                       [k k]) ks)))]
      (keys-spec (parse-keys (unquote-form (:req args)))
                 (parse-keys (unquote-form (:req-un args)))
                 (parse-keys (unquote-form (:opt args)))
                 (parse-keys (unquote-form (:opt-un args)))))))

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
    (keys-spec (:req state) (:req-un state) {} {})))

(defmethod parse-spec* :set [x]
  (or- (mapv parse-spec x)))

(defmethod parse-spec* :coll [x]
  (cond
    (sequential? x) (parse-spec-seq x)
    (map? x) (parse-spec-map x)))

(s/fdef merge-keys :args (s/cat :ks (s/coll-of keys-spec?)) :ret keys-spec?)
(defn merge-keys [ks]
  (->> ks
       (mapv parse-spec)
       (apply merge-with merge)
       (p/map->KeysSpec)))

(defn coll-of-map? [s]
  (and (coll-of? s) (= map? (:kind s))))

(declare merge-specs)
(s/fdef merge-or-keys :args (s/cat :or or? :key keys-spec?) :ret or?)
(defn merge-or-keys [o k]
  (or- (mapv (fn [p]
               (merge-specs p k)) (:ps o))))

(defn merge-specs [& specs]
  (reduce (fn [s1 s2]
            (let [s1 (parse-spec s1)
                  s2 (parse-spec s2)]
              (cond
                (and (keys-spec? s1) (keys-spec? s2)) (merge-keys [s1 s2])
                (and (or? s1) (keys-spec? s2)) (merge-or-keys s1 s2)
                (and (keys-spec? s1) (or? s2)) (merge-or-keys s2 s1)
                :else (and- [s1 s2])))) specs))

(s/fdef conform-map-of :args (s/cat :m ::spect :v value?) :ret any?)
(defn conform-map-of [map-of v]
  {:pre [(value? v) (map? (:v v))]}
  (when (and (every? (fn [k]
                       (valid? (:ks map-of) k)) (keys (:v v)))
             (every? (fn [v]
                       (valid? (:vs map-of) v)) (vals (:v v))))
    v))

(defn map-of? [x]
  (instance? MapOf x))

(extend-type MapOf
  p/Spect
  (conform* [{:keys [ks vs] :as this} x]
    (cond
      (instance? spectrum.protocols.MapOf x) (when (and (valid? (parse-spec ks) (parse-spec (:ks x)))
                                                        (valid? (parse-spec vs) (parse-spec (:vs x))))
                                               x)
      (and (value? x) (map? (:v x))) (conform-map-of this x)
      :else nil))
  p/DependentSpecs
  (dependent-specs- [s]
    #{(class-spec clojure.lang.PersistentHashMap)})
  p/Truthyness
  (truthyness [this]
    :truthy)
  p/Invoke
  (invoke- [{:keys [ks vs] :as this} args]
    (assert (cat? args))
    (let [arg-count (count (:ps args))
          k (first- args)
          direct-hit (parse-spec vs)
          else (or (second- args) (value nil))
          partial-hit (or- [(parse-spec vs) else])]
      (if (contains? #{1 2} arg-count)
        (->> ks
             (parse-spec)
             (disentangle)
             (mapcat (fn [ks]
                       (map (fn [xs]
                              (if (valid? ks xs)
                                (if (value? ks)
                                  direct-hit
                                  partial-hit)
                                else)) (disentangle k))))
             (filter identity)
             (or- ))
        (invalid {:message (format "wrong number of args passed to %s, got %s" (print-str this) (print-str args))})))))

(extend-regex MapOf)
(will-accept-this MapOf)

(defn map-of [key-pred val-pred]
  (p/map->MapOf {:ks key-pred
                 :vs val-pred}))

(defn parse-map-of [x]
  (let [[form pred opts] (rest x)
        tuple (unquote-form form)
        [_ k v] tuple]
    (p/map->MapOf {:ks (parse-spec k)
                   :vs (parse-spec v)})))

(defmethod parse-spec* `s/every [x]
  (parse-coll-of x))

(defmethod parse-spec* `s/every-impl [x]
  (let [[form pred opts] (rest x)
        form (unquote-form form)
        s (parse-spec form)
        empty-kind (get kind->coll (get opts :kind))]
    (if (= 'clojure.core/map? (:kind opts))
      (parse-map-of x)
      (p/map->CollOfSpec (merge {:s s
                                 :empty-kind empty-kind} opts)))))

(defmethod parse-spec* `s/coll-of [x]
  (parse-coll-of x))

(defmethod parse-spec* `s/map-of [x]
  (let [k (nth x 1)
        v (nth x 2)]
    (map-of k v)))

(defmethod parse-spec* `s/merge [x]
  (apply merge-specs (rest x)))

(defmethod parse-spec* `s/merge-spec-impl [x]
  (let [[forms preds & _] (rest x)
        forms (unquote-form forms)]
    (apply merge-specs forms)))

(defmethod parse-spec* `s/conformer [x]
  (value true))

(defmethod parse-spec* `s/nonconforming [x]
  (parse-spec* (second x)))


(extend-regex FnSpec)
(will-accept-this FnSpec)

(predicate-spec fn-spec?)
(defn fn-spec? [x]
  (instance? spectrum.protocols.FnSpec x))

(s/def :fn-spec/args (s/nilable ::valid-spect-like))
(s/def :fn-spec/ret (s/nilable ::valid-spect-like))
(s/def :fn-spec/fn (s/nilable ::valid-spect-like))

(s/fdef fn-spec :args (s/cat :args :fn-spec/args :ret :fn-spec/ret :fn :fn-spec/fn))
(s/fdef map->FnSpec :args (s/cat :m (s/keys :opt-un [:fn-spec/args :fn-spec/ret :fn-spec/fn])) :ret ::valid-spect)

(defn fn-spec [args ret f]
  {:pre []}
  (let [invalid-args (->>
                      {:args args :ret ret :fn f}
                      (remove (fn [[k v]]
                                (when v
                                  (conformy? v))))
                      (filter (fn [[k v]]
                                (identity v))))]
    (if (seq invalid-args)
      (do
        (println "fn-spec invalid args:" args ret)
        (assert false)
        (invalid {:message (format "invalid fn: %s" (print-str (into {} invalid-args)))}))
      (p/map->FnSpec {:args args
                      :ret ret
                      :fn f}))))

(s/fdef merge-fn-specs :args (s/cat :specs (s/coll-of ::spect) :ret ::spect))
(defn merge-fn-specs
  "Given a seq of fn-spec representing the arities for a fn, merge them into one fn-spec"
  [fn-specs]
  (if (every? fn-spec? fn-specs)
    (let [args (or- (filter identity (map :args fn-specs)))
          rets (or- (map :ret fn-specs))]
      (fn-spec args rets nil))
    (or
     (first (filter invalid? fn-specs))
     (invalid {:message (format "can't merge fn-specs: %s" (mapv print-str fn-specs))}))))

(s/fdef get-var-spec :args (s/cat :v var?) :ret (s/nilable ::spect))
(defn get-var-spec [v]
  (when-let [s (s/get-spec v)]
    (assoc (parse-spec s) :var v)))

(defn var-named-predicate?
  "True if the var's name looks like a predicate"
  [v]
  (boolean (re-find #"\?$" (name (.sym ^Var v)))))

(s/fdef var-predicate? :args (s/cat :v var?) :ret boolean?)
(defn var-predicate?-
  [v]
  (let [s (get-var-spec v)]
    (if s
      (and (-> s :args cat?)
           (-> s :args :ps count (= 1))
           (-> s :ret (= (pred-spec #'boolean?)))
           (var-named-predicate? v))
      false)))

(def var-predicate? (memo/memo var-predicate?-))

(defn valid-transformation?
  "True if a spec transformer can transform from A->B"
  [a b]
  (or (valid? a b) (invalid? b) (unknown? b)))

(s/fdef maybe-transform :args (s/cat :s ::spect :args ::spect) :ret ::spect)
(defn maybe-transform [spec args]
  {:post [(do
            (when-not (spect? %)
              (println "transform failed:" spec %)) true)
          (spect? %)]}
  (if (not (:transformed spec))
    (if-let [v (:var spec)]
      (if-let [t (data/get-invoke-transformer v)]
        (let [spec spec
              spec* (t spec args)
              transformed? (not= spec spec*)]
          (if transformed?
            (if (valid-transformation? (assoc spec :args args) spec*)
              (assoc spec* :transformed true)
              (invalid {:message (format "transformed fn must conform to original spec. original: %s  with args %s transformed: %s" (print-str spec) (print-str args) (print-str spec*))}))
            spec))
        spec)
      spec)
    spec))

(defn every-valid? [s]
  (every? #(conformy? %) (coll-items s)))

(defn every-known? [s]
  (every? #(known? %) (coll-items s)))

(s/fdef invoke-fn-spec :args (s/cat :s fn-spec? :args ::spect) :ret ::spect)
(defn invoke-fn-spec [spec invoke-args]
  {:post [(do (when-not (spect? %)
                (println "invoke failed:" spec %)) true) (spect? %)]}
  (let [v (:var spec)
        args (parse-spec (:args spec))]
    (if args
      (if (valid? args invoke-args)
        (let [spec* (maybe-transform spec invoke-args)]
          (if (not (invalid? spec*))
            (if-let [ret (:ret spec*)]
              (parse-spec ret)
              (pred-spec #'any?))
            spec*))
        (if (every-known? invoke-args)
          (if (every-valid? invoke-args)
            (invalid {:message (format "invoke-fn-spec can't invoke %s (%s) with %s => %s" v (print-str args) (print-str invoke-args) (print-str (conform args invoke-args)))})
            (invalid {:message (format "invoke with invalid args %s" (print-str invoke-args))}))
          (unknown {:message (format "invoke %s w/ unknown args %s" v (print-str invoke-args))})))
      (unknown {:message (format "invoke %s no :args spec" spec)}))))

(extend-type FnSpec
  p/Spect
  (conform* [this x]
    (when (and (instance? spectrum.protocols.FnSpec x)
               (or
                (and (:var this)
                     (:var x)
                     (= (:var this)
                        (:var x)))
                (and
                 (if (:args this)
                   (if (:args x)
                     (if (valid? (:args this) (:args x))
                       x
                       false)
                     false)
                   x)
                 (if (:ret this)
                   (if (:ret x)
                     (if (valid? (:ret this) (:ret x))
                       x
                       false)
                     false)
                   x)
                 (if (:fn this)
                   (if (:fn x)
                     (if (valid? (:fn this) (:fn x))
                       x
                       false)
                     false)
                   x))))
      x))
  (explain* [spec path via in x]
    (when-not (valid? spec x)
      [{:path path :pred spec :val x :via via :in in}]))
  p/DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'fn?) (pred-spec #'ifn?)})
  p/Invoke
  (invoke- [this args]
    (invoke-fn-spec this args))
  (invoke-accept- [this]
    (if (:args this)
      (:args this)
      (unknown {:message (format "no :args spec on %s" this)})))
  p/Truthyness
  (truthyness [this]
    :truthy))

(defmethod parse-spec* `s/fspec [x]
  (let [pairs (->> x rest (partition 2))
        pairs (map (fn [[k p]]
                     (when p
                       [k (parse-spec p)])) pairs)
        args (into {} pairs)]
    (p/map->FnSpec args)))

(defmethod parse-spec* `s/fspec-impl [x]
  (let [[arg-spec arg-form ret-spec ret-form fn-spec fn-form gen-fn] (rest x)
        args (unquote-form arg-form)
        ret (unquote-form ret-form)
        fn (unquote-form fn-form)
        args (when args
               (parse-spec args))
        ret (when ret
              (parse-spec ret))
        fn (when fn
             (parse-spec fn))]
    (p/map->FnSpec (merge (when arg-spec
                            {:args args})
                          (when ret-spec
                            {:ret ret})
                          (when fn-spec
                            {:fn fn})))))

(defn maybe-resolve-keyword-spec [x]
  (if (and (value? x) (keyword? (:v x)) (#'s/maybe-spec (:v x)))
    (parse-spec (s/spec (:v x)))
    x))

(s/fdef valid-invoke? :args (s/cat :s ::spect :args ::spect) :ret boolean?)
(defn valid-invoke?
  "check that fnspec can be invoked w/ args"
  [spec args]
  (cond
    (unknown? spec) spec
    (fn-spec? spec) (valid? (:args spec) args)
    :else (invalid {:message (format "can't invoke %s" (print-str spec))})))

(s/fdef conform-pred-args? :args (s/cat :p pred-spec? :x ::spect) :ret boolean?)
(defn conform-pred-args?
  [pred-spec args-spect]
  (println "conform pred args:" pred-spec args-spect)
  (if-let [fn-spec (resolve-pred-spec pred-spec)]
    (valid-invoke? fn-spec args-spect)
    false))

(defn multispec [method retag]
  (p/map->MultiSpec {:multimethod method
                     :retag retag}))

(predicate-spec multispec?)
(defn multispec? [x]
  (instance? spectrum.protocols.MultiSpec x))

(s/fdef multispec-dispatch-ret-value :args (s/cat :ms multispec? :val any?) :ret ::spect)
(defn multispec-assoc-retag
  "Given a concrete instance of a multispec, update it to include the dispatch value"
  [ms spec dispatch-value]
  (let [{:keys [retag]} ms
        key-type (if (simple-keyword? retag)
                   :req-un
                   :req)
        existing-key-spec (get-in spec [key-type retag])]
    (when-not existing-key-spec
      (println "Multispec assoc retag:" ms spec key-type retag))
    (assert existing-key-spec)
    (assert (valid? (parse-spec existing-key-spec) dispatch-value))
    (assoc-in spec [key-type retag] dispatch-value)))

(s/fdef multispec-dispatch-ret-value :args (s/cat :ms multispec? :val ::spect) :ret ::spect)
(defn multispec-dispatch-ret-value
  "Given a dispatch value, return the spec"
  [ms dispatch-value]
  {:pre [(spect? dispatch-value)]}
  (let [v (:multimethod ms)
        retag (:retag ms)
        s (v {retag dispatch-value})
        _ (assert s)
        s (parse-spec s)
        s (multispec-assoc-retag ms s dispatch-value)]
    (if s
      s
      (unknown {:form [v dispatch-value]}))))

(defn multispec-dispatch-invoke [ms v]
  {:pre [(var? (:retag ms))
         (fn? (:retag ms))
         (spect? v)]}
  (if-let [s (get-var-spec (:retag ms))]
    (if-let [t (data/get-invoke-transformer v)]
      (let [fn-spec* (t s v)]
        (:ret fn-spec*))
      (:ret s))
    (do
      (println "no spec for" (:retag ms))
      ::no-dispatch)))

(defn multispec-dispatch
  [ms x]
  (cond
    (keyword? (:retag ms)) (or (when (keys-contains? x (:retag ms))
                                 (let [d (keys-get x (:retag ms))]
                                   (if (value? d)
                                     d
                                     ::no-dispatch)))
                               ::no-dispatch)
    (fn? (:retag ms)) (multispec-dispatch-invoke ms x)))

(defn multispec-default-spec
  "When we can't determine the correct multispec dispatch value, get the lowest common denominator spec, Or'ing all of the possible values together"
  [ms]
  (->>
   @(:multimethod ms)
   (multimethod-dispatch-values )
   (map parse-spec)
   (map (fn [v]
          (multispec-dispatch-ret-value ms v)))
   (or- )))

(defn multispec-resolve-spec
  "Given a multispec and a dispatch value, attempt to return the spec for that defmethod call. Returns specific spec, or multispec-default-spec"
  [ms v]
  (let [d (multispec-dispatch ms v)]
    (if (not= d ::no-dispatch)
      (multispec-dispatch-ret-value ms d)
      (multispec-default-spec ms))))

(extend-type MultiSpec
  p/Spect
  (conform* [this x]
    (let [dispatch-type (cond
                          (keyword? (:retag this)) :keyword
                          (fn? (:retag this)) :fn
                          :else (assert false "unknown dispatch type"))]
      (cond
        (and (multispec? x) (= (:multimethod this) (:multimethod x))) x
        (= :keyword dispatch-type) (when (valid? (pred-spec #'map?) x)
                                     (let [s (multispec-resolve-spec this x)]
                                       (conform s x)))
        (= :fn dispatch-type) (when (valid-invoke? (:retag this) x)
                                (conform (multispec-resolve-spec this x) x)))))
  p/DependentSpecs
  (dependent-specs- [this]
    (p/dependent-specs- (multispec-default-spec this)))
  p/KeywordInvoke
  (keyword-invoke- [this k]
    (keyword-invoke (multispec-default-spec this) k))
  p/WillAccept
  (will-accept- [this]
    (->>
     @(:multimethod this)
     (multimethod-dispatch-values)
     (map parse-spec)
     (mapv (fn [v]
             (multispec-dispatch-ret-value this v)))
     or-))
  p/Truthyness
  (truthyness [this]
    (p/truthyness (multispec-default-spec this))))

(extend-regex MultiSpec)

(defn maybe-spec-spec [x]
  (if (seq? x)
    (spec-spec x)
    x))

(defn maybe-transform-method
  "apply the java method transformer, if applicable"
  [meth spec args]
  (if-let [t (data/get-invoke-transformer meth)]
    (let [spec* (t spec args)]
      (if (valid-transformation? spec spec*)
        spec*
        (invalid {:message (format "transformed fn must conform to original spec. original: %s  with args %s transformed: %s" (print-str spec) (print-str args) (print-str spec*))})))
    spec))

(defmethod parse-spec* `s/multi-spec [x]
  (let [retag (nth x 2)
        retag (cond
                (keyword? retag) retag
                (symbol? retag) (resolve retag))
        method (resolve (nth x 1))]
    (assert retag)
    (multispec method retag)))

(defmethod parse-spec* `s/multi-spec-impl [x]
  (let [[form mmvar-form retag] (rest x)
        mmvar (resolve (second mmvar-form))]
    (assert (var? mmvar))
    (multispec-default-spec (multispec mmvar retag))))

(extend-protocol p/Spect
  clojure.spec.alpha.Spec
  (conform* [spec x]
    (p/conform* (parse-spec spec) (parse-spec x))))

(extend-type clojure.spec.alpha.Spec
  p/Spect
  (conform* [spec x]
    (p/conform* (parse-spec* spec) x)))

(s/fdef re-conform :args (s/cat :s ::spect :d ::spect) :ret ::spect)
(defn re-conform [spec data]
  (let [spec* spec
        data* data]
    (loop [spec spec
           data data
           iter 0]
      (if (> iter 100)
        (do (println "infinite re-conform:" spec* data*)
            (assert false)
            (invalid {:message "infinite"}))
        (if (first-rest? data)
          (let [x (first- data)]
            (if (nil? x)
              (if (accept-nil? spec)
                (let [r (return spec)]
                  (if (nil? r)
                    (value nil)
                    r))
                (invalid {:message (format "%s does not conform to %s" (print-str data) (print-str spec))}))
              (if-let [dp (derivative spec x)]
                (if (conformy? dp)
                  (if (and (infinite? dp) (accept-nil? dp) (infinite? (rest- data)))
                    (return dp)
                    (recur dp (rest- data) (inc iter)))
                  (invalid {:message (format "%s does not conform to %s" (print-str data) (print-str spec))}))
                (invalid {:message (format "%s does not conform to %s" (print-str data) (print-str spec))}))))
          reject)))))

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
        (p/re-explain* spec path via (conj in i) data)))))

(s/fdef value-invoke-dispatch :args (s/cat :f ::spect :args ::spect) :ret keyword?)
(defn value-invoke-dispatch [f args]
  (assert (first-rest? args))
  (let [val f
        obj (first- args)
        else (second- args)
        rest (rest- (rest- args))]
    (assert (value? val))
    (cond
      (var? (:v f)) :var
      (ifn? (:v f)) :fn
      (not obj) :invalid
      rest :invalid
      (and (value? obj) (nil? else)) :value-value
      (and (value? obj) (value? else)) :value-value-else
      (and (coll-of? obj) (nil? else)) :value-coll-of
      (and (coll-of? obj) else) :value-coll-of-else
      :else :unknown)))

(defmulti value-invoke "" #'value-invoke-dispatch)

(defmethod value-invoke :value-value [spec args]
  (let [f (:v spec)
        arg (first- args)
        arg (:v arg)]
    (if (ifn? f)
      (value (get f arg))
      (invalid {:message (format "can't invoke %s" (print-str f))}))))

(defmethod value-invoke :value-value-else [spec args]
  (let [key (:v spec)
        obj (first- args)
        obj (:v obj)
        [key obj] (cond
                    (and (keyword? key) (coll? obj)) [key obj]
                    (and (coll? key) (keyword? obj)) [obj key]
                    :else [key obj])
        else (second- args)]
    (if-let [ret (get obj key)]
      (value ret)
      else)))

(defmethod value-invoke :value-coll-of [spec args]
  (unknown {:message "not yet implemented"}))

(defmethod value-invoke :value-coll-of-else [spec args]
  (unknown {:message "not yet implemented"}))

(defmethod value-invoke :var [spec args]
  (let [v (:v spec)]
    (if-let [s (get-var-spec v)]
      (invoke s args)
      (unknown {:message (format "value-invoke: no spec for %s" v)}))))

(defmethod value-invoke :fn [spec args]
  (unknown {:message (format "no spec for fn invoke %s" (print-str spec))}))

(defmethod value-invoke :invalid [f args]
  (let [val f
        obj (first- args)
        else (second- args)
        rest (rest- (rest- args))]
    (cond
      (not obj) (invalid {:message "not enough args to invoke"})
      rest (invalid {:message (format "too many args to invoke %s, got %s" (print-str val) (print-str args))})
      :else (assert false))))

(defmethod value-invoke :unknown [spec args]
  (unknown {:message (format "value-invoke unknown: don't know how to invoke %s %s" (print-str spec) args)}))

(defmulti value-invoke "" #'value-invoke-dispatch)

(defn value-invoke-accept [v]
  (let [v* v
        v (:v v)]
    (cond
      (vector? v) (cat- [v (pred-spec #'nat-int?)])
      (set? v) (cat- [v (pred-spec #'any?)])
      (map? v) (or- [(cat- [v (pred-spec #'any?)]) (cat- [v (pred-spec #'any?) (pred-spec #'any?)])])
      (or (keyword? v) (symbol? v)) (or- [(cat- [v (pred-spec #'any?)]) (cat- [v (pred-spec #'any?) (pred-spec #'any?)])])
      (nil? v) (invalid {:message "can't invoke nil"})
      :else (do
              (println "unknown value-invoke:" v* (class v))
              (assert false (format "unknown value invoke: %s" (print-str v*)))))))

(def spect-generator (gen/elements [(pred-spec #'int?) (class-spec Long) (value true) (value false) (unknown nil)]))

(defn conform-strategy [spec args]
  (let [spec-or (or? spec)
        spec-and (and? spec)
        args-or (or? args)
        args-and (and? args)]
    (cond
      (and spec-and args-and) :and-and
      (and spec-or args-or) :or-or
      ;; (and spec-and args-or) :and-or
      (and spec-or args-and) :or-and
      spec-and :spec-and
      args-and :args-and
      args-or :args-or
      :else :simple)))

(defmulti conform-compound #'conform-strategy)

(defmethod conform-compound :and-and [spec args]
  (when (every? (fn [p]
                  (some #(valid? p %) (->> args :ps (map parse-spec)))) (map parse-spec (:ps spec)))
    args))

(defmethod conform-compound :or-or [spec args]
  (when (every? (fn [arg]
                  (valid? spec arg)) (map parse-spec (:ps args)))
    args))

(defmethod conform-compound :or-and [spec args]
  (when (some (fn [arg]
                (some (fn [s]
                        (valid? s arg)) (map parse-spec (:ps spec)))) (map parse-spec (:ps args)))
    args))

(defmethod conform-compound :spec-and [spec args]
  (when (every? (fn [p]
                  (valid? p args)) (map parse-spec (:ps spec)))
    args))

(defmethod conform-compound :args-and [spec args]
  (when (some (fn [arg]
                (valid? spec arg)) (map parse-spec (:ps args)))
    args))

(defmethod conform-compound :args-or [spec args]
  (when (every? (fn [arg]
                  (valid? spec arg)) (map parse-spec (:ps args)))
    args))

(defmethod conform-compound :simple [spec args]
  (p/conform* spec args))

(def ^:dynamic *conform-in-progress* #{})

(defn conform-bfs [spec args]
  (let [args-orig args]
    (if (contains? *conform-in-progress* [spec args])
      (invalid {:message (format "%s does not conform to %s" (print-str args-orig) (print-str spec))})
      (binding [*conform-in-progress* (conj *conform-in-progress* [spec args])]
        (loop [args args
               q (queue)
               seen #{}]
          (let [val (conform-compound spec args)]
            (cond
              (and val (conformy? val)) args-orig
              (invalid? val) val
              (or (reject? val) (nil? val)) (let [ds (dependent-specs args)
                                                  _ (assert (set? seen))
                                                  ds (set/difference ds seen)
                                                  q (concat q ds)]
                                              (if (seq q)
                                                (recur (first q) (rest q) (set/union seen ds))
                                                (invalid {:message (format "%s does not conform to %s" (print-str args-orig) (print-str spec))})))
              :else (do (println "conform bfs " spec args "=>" val "unhandled") (assert false)))))))))


(s/fdef conform- :args (s/cat :s ::spect :args ::spect) :ret ::spect)
(defn conform-
  "Given a spect and args, return the conforming parse. Behaves similar
  to s/conform, but args must be spectrum spects, rather than clojure.specs"
  [spec args]
  {:post [(s/valid? ::spect %)]}
  (try
    (conform-bfs spec args)
    (catch Throwable e
      (println "conform: kaboom:" spec args (.getMessage e))
      (throw e))))

(def ^:dynamic *conform-cache* false)

(def conform (if *conform-cache*
               (memo/lru conform- :lru/threshold 10000)
               conform-))

(s/fdef valid? :args (s/cat :s ::spect :args (s/nilable ::spect)) :ret boolean?)
(defn valid? [spec x]
  (conformy? (conform spec x)))

(s/fdef valid-return? :args (s/cat :s ::spect :args ::spect) :ret boolean?)
(defn valid-return?
  "True if spec conforms, as a return value"
  [spec args]
  (and (not (control-flow? args))
       (valid? spec args)))

(defn valid-return-java?
  "True if spec conforms, in a java interop context"
  [spec args]
  (or (valid? spec args)
      (every? identity (for [sc (spec->classes spec)
                             ac (spec->classes args)]
                         (or (valid? (class-spec sc) (class-spec ac))
                             (j/castable? sc ac))))))

(defn explain-data [spec x]
  (p/explain* spec [] [] [] x))

(defn explain-out [data])

(defn explain [spec args]
  (explain-data spec args))

(defmethod print-method Unknown [spec ^Writer w]
  (let [{:keys [file line column]} spec]
    (.write w (str "#unknown[" (if (seq (:message spec))
                                 (:message spec)
                                 (print-method (:form spec) w))
                   (when file
                     (str file line column)) "]"))))

(defn regex-print-method [re-name spec ^Writer w]
  (.write w (str "#" re-name ))
  (#'clojure.core/print-sequential "[" print-method " " "]" (:ps spec) w))

(defmethod print-method RegexCat [v ^Writer w]
  (regex-print-method "cat" v w))

(defmethod print-method RegexSeq [v ^Writer w]
  (regex-print-method "seq" {:ps (take 1 (:ps v))} w))

(defmethod print-method RegexAlt [v ^Writer w]
  (regex-print-method "alt" v w))

(defmethod print-method Value [v ^Writer w]
  (.write w "#value[")
  (print-method (:v v) w)
  (.write w "]"))

(defmethod print-method PredSpec [v ^Writer w]
  (.write w (format "#pred " ))
  (print-method (:form v) w))

(defn class-name [c])
(defmethod print-method spectrum.protocols.ClassSpec [v ^Writer w]
  (.write w "#class ")
  (.write w (.getCanonicalName ^Class (:cls v))))

(defmethod print-method AndSpec [v ^Writer w]
  (.write w "#and")
  (#'clojure.core/print-sequential "[" print-method " " "]" (:ps v) w))

(defmethod print-method OrSpec [v ^Writer w]
  (.write w (format "#or"))
  (#'clojure.core/print-sequential "[" print-method " " "]" (:ps v) w))

(defmethod print-method NotSpec [v ^Writer w]
  (.write w "#not[")
  (print-method (:s v) w)
  (.write w "]"))

(defmethod print-method FnSpec [s ^Writer w]
  (.write w "#fn")
  (->> (map #(find s %) [:var :args :ret :fn])
       (filter (fn [[k v]]
                 (identity v)))
       (apply concat)
       (vec)
       (#(print-method % w))))

(defmethod print-method KeysSpec [spec ^Writer w]
  (.write w "#keys{")
  (doseq [type [:req :req-un :opt :opt-un]
          keys (get spec type)
          :when keys]
    (.write w (str type))
    (#'clojure.core/print-sequential "{" print-method " " "}" keys w))
  (.write w "}"))

(defmethod print-method CollOfSpec [spec ^Writer w]
  (let [[open close] (condp = (:kind spec)
                       map? ["{" "}"]
                       vector? ["[" "]"]
                       set? ["#{" "}"]
                       ["[" "]"])]
    (.write w "#coll")
    (#'clojure.core/print-sequential open print-method " " close [(:s spec)] w)))

;; Readers
(defn read-pred [p]
  (pred-spec (resolve p)))

(defn read-value [v]
  (value v))

(defn read-or [ps]
  (or- ps))

(defn read-and [ps]
  (and- ps))

(defn read-fn [ps]
  (let [ps (apply hash-map ps)]
    (fn-spec (:args ps) (:ret ps) (:f ps))))

(defn read-cat [ps]
  (cat- ps))

(defn read-class [p]
  (assert (symbol? p))
  (class-spec (resolve p)))

(defn read-not [p]
  (not- p))

(set! *data-readers* (merge *data-readers* {'and #'read-and
                                            'cat #'read-cat
                                            'class #'read-class
                                            'fn #'read-fn
                                            'not #'read-not
                                            'or #'read-or
                                            'pred #'read-pred
                                            'value #'read-value}))

;; #(gen/one-of (map (fn [s] (-> s s/spec s/gen)) #{::pred-spec ::value ::coll-of-spec}))

(defn not-self-recursive-gen
  "Takes an fmap fn, a such-that pred and an inner generator. Returns a recursive generator that is such-that most of the time"
  [f-m such-that-pred inner-gen]
  (gen/fmap f-m (gen/frequency [[9 (gen/such-that such-that-pred inner-gen)]
                                [1 inner-gen]])))

(defn not-self-recursive-coll-gen
  "Takes an fmap fn, a such-that pred and an inner generator. Returns a recursive generator that is such-that most of the time"
  [f-m such-that-pred inner-gen outer-gen-fn]
  (gen/fmap f-m (outer-gen-fn (gen/frequency [[9 (gen/such-that such-that-pred inner-gen)]
                                              [1 inner-gen]]))))

(declare simple-gen)

;; (gen/fmap #(not- %) (gen/frequency [[9 (s/gen ::pred)]
;;                                       [1 (gen/delay (simple-gen))]]))

;; (defn not-gen []
;;   (gen/fmap #(not- %) (gen/frequency [[9 (s/gen ::pred)]
;;                                       [1 (gen/delay (simple-gen))]])))

(defn simple-spec-gen []
  (gen/frequency [[3 (s/gen ::pred)]
                  [1 (s/gen ::value)]
                  [1 (s/gen ::coll-of)]
                  [1 (s/gen ::or)]
                  ;; [1 (s/gen ::and)]
                  [1 (s/gen ::map-of)]
                  ]))

(s/def ::pred (s/with-gen pred-spec? #(gen/fmap (fn [p] (pred-spec p)) spectrum.gen/core-predicates-gen)))
(s/def ::value (s/with-gen value? #(gen/fmap (fn [x] (value x)) (s/gen (s/spec any?)))))

(s/def ::coll-of (s/with-gen coll-of? (fn [] (gen/fmap #(coll-of %) (gen/delay (s/gen ::spect))))))

(s/def ::not (s/with-gen not? (fn [] (gen/fmap #(not- %) (gen/delay (s/gen ::spect))))))

(s/def ::or (s/with-gen or? (fn [] (gen/fmap #(or- %) (gen/delay (gen/vector (s/gen ::spect) 2 5))))))

(s/def ::and (s/with-gen and? (fn [] (gen/fmap #(and- %) (gen/delay (gen/vector (simple-spec-gen) 2 5))))))

(s/def ::map-of (s/with-gen map-of? (fn [] (gen/fmap (fn [[k v]] (map-of k v)) (gen/delay (gen/vector (simple-spec-gen) 2))))))

;; non-regex

(defn spec-gen []
  (gen/frequency
   [[3 (simple-spec-gen)]
    [1 (s/gen ::cat)
     1 (s/gen ::alt)
     1 (s/gen ::seq)]]))

;; regex
(s/def ::cat (s/with-gen cat? (fn [] (gen/fmap #(cat- %) (gen/vector (gen/delay (spec-gen)) 0 5)))))
(s/def ::alt (s/with-gen alt? (fn [] (gen/fmap #(alt- %) (gen/delay (gen/vector (spec-gen) 1 3))))))
(s/def ::seq (s/with-gen seq? (fn [] (gen/fmap (fn [p] (seq- p)) (gen/delay (spec-gen))))))

(s/def ::spect (s/with-gen spect? simple-spec-gen))
