(ns spectrum.conform
  (:require [clojure.core.memoize :as memo]
            [clojure.reflect :as reflect]
            [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.util :refer [fn-literal? print-once strip-namespace var-name queue queue? predicate-spec validate! conj-seq multimethod-dispatch-values protocol?]]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.java :as j])
  (:import (clojure.lang Var Keyword)
           java.io.Writer))

(declare conform)
(declare valid?)
(declare parse-spec)
(declare value)

(declare class-spec?)
(declare pred-spec?)
(declare or-spec?)

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

(defprotocol Spect
  (conform* [spec x]
    "Return the conforming value or invalid")
  (explain* [spec path via in x]))

(predicate-spec spect?)
(defn spect? [x]
  (and (instance? clojure.lang.IRecord x) (satisfies? Spect x)))

(s/def ::spect spect?)

(s/fdef conform* :args (s/cat :s spect? :x any?) :ret (s/nilable spect?))

(defprotocol Compound
  (map- [spec f])
  (filter- [spec f])
  (new- [spec ps]))

(predicate-spec compound-spec?)
(defn compound-spec? [x]
  (satisfies? Compound x))

(defprotocol DependentSpecs
  (dependent-specs- [spec]
    "Extra specs that are true of every instance of this type."))

(defprotocol KeysGet
  (keys-get- [this key]))

(defn keys-get? [s]
  (satisfies? KeysGet s))

(defn dependent-specs? [s]
  (satisfies? DependentSpecs s))

(defn map* [f spec]
  (map- spec f))

(defn filter* [f spec]
  (if (compound-spec? spec)
    (filter- spec f)
    (when (f spec)
      spec)))

(defn apply-some
  "Apply f with spec and args. If spec is singular, applies f once. If spec is compound (such as `or` or `and`), apply to each eleement, returning truthy if f returns truthy on any element"
  [f spec & args]
  (if (compound-spec? spec)
    (some identity (map* (fn [s*]
                           (apply f s* args)) spec))
    (apply f spec args)))

(defn apply-every
  "Apply f with spec and args. If spec is singular, applies f once. If spec is compound (such as `or` or `and`), apply to each element, returning truthy if f returns truthy for every element"
  [f spec & args]
  (if (compound-spec? spec)
    (every? identity (map* (fn [s*]
                             (apply f s* args)) spec))
    (apply f spec args)))

(defn apply-map
  "Like the other applies-, works on compound and not. Always returns a collection"
  [f spec & args]
  (if (compound-spec? spec)
    (do
      (assert (:ps spec))
      (map (fn [s*]
              (apply f s* args)) (:ps spec)))
    [(apply f spec args)]))

(defn remove* [f spec]
  (filter- spec (complement f)))

(defprotocol WillAccept
  (will-accept- [spec]
    "Return the spect that will make (derivative spec x) return truthy (not reject/invalid). Return nil when the spect is a regex, but complete. Return reject/invalid when it isn't legal to call derivative on spect"))

(defprotocol SpecToClasses
  (spec->classes- [this]))

(declare spec->classes)

(defprotocol Regex
  (derivative
    [spec x]
    "Given a parsed spec, return the derivative")
  (re-explain* [spec path via in x])
  (empty-regex [this]
    "The empty pattern for this regex")
  (accept-nil? [this]
    "True if this pattern successfully matches")
  (return- [this]
    "Given a completed regex parse, return the conform matching value")
  (with-return- [this ret]
    "add this regex's return data to ret")
  (regex? [this]
    "True if this spec is actually a regex, and not just a normal spec implementing the protocol"))

(defn singular? [x]
  (not (regex? x)))

(s/def :with-return/ret (s/or :s (s/nilable spect?) :coll (s/coll-of (s/or :s spect? :ret :with-return/ret) :kind vector?)))

(defrecord Accept [ret])

(defrecord Reject [])

(s/fdef accept :args (s/cat :x (s/or :s spect? :wr :with-return/ret)) :ret spect?)
(defn accept [x]
  (map->Accept {:ret x}))

(def reject (map->Reject {}))

(defn accept? [x]
  (instance? Accept x))

(defn reject? [x]
  (instance? Reject x))

(defrecord Invalid [a-loc form message])

(s/fdef return :args (s/cat :s :with-return/ret) :ret (s/nilable spect?))
(defn return [s]
  {:post [(validate! (s/nilable spect?) %)]}
  (validate! (s/or :accept accept? :accept-nil accept-nil? :not-re singular?) s)
  (let [ret (return- s)]
    (validate! :with-return/ret ret)
    (if (vector? ret)
      (cat- (mapv return ret))
      ret)))

(s/fdef with-return :args (s/cat :this (s/nilable spect?) :ret :with-return/ret) :ret (s/nilable spect?))
(defn with-return [s ret]
  {:post [(validate! :with-return/ret %)]}
  (with-return- s ret))

(s/def ::will-accept-ret (s/nilable spect?))
(s/fdef will-accept :args (s/cat :s spect?) :ret spect?)
(defn will-accept [s]
  {:post [(do (when-not (s/valid? ::will-accept-ret %) (println "invalid will-accept:" s "=>" %)) true) (s/valid? ::will-accept-ret %)]}
  (will-accept- s))

(s/fdef keys-get :args (s/cat :s spect? :k keyword?) :ret spect?)
(defn keys-get [s k]
  {:post [(s/valid? spect? %)]}
  (if (keys-get? s)
    (keys-get- s k)
    (value nil)))

(defprotocol FirstRest
  (first- [this])
  (rest- [this]
    "Return a spect or nil.

    Returns nil if it's legal to call rest on this, but there are no
    items. Return invalid if it's not legal to call rest,
    i.e. (value :foo)"))

(defprotocol Truthyness
  (truthyness [this]
    "The truthyness of this spec, if it appeared in an `if`. Returns :truthy, :falsey or :ambiguous"))

(s/fdef invoke :args (s/cat :s spect? :args spect?) :ret spect?)
(defprotocol Invoke
  (invoke- [s args]
    "if code calls (s args), return the expected return type")
  (invoke-accept- [s]
    "Return the most general spec this spec can be invoked with"))

(s/fdef keyword-invoke :args (s/cat :s spect? :args spect?) :ret spect?)
(defprotocol KeywordInvoke
  (keyword-invoke [s args]
    "If code calls (:foo spec), return the expected type"))

(defn keyword-invoke? [s]
  (satisfies? KeywordInvoke s))

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

(s/def ::spect (s/and spect? map?))
(s/def ::valid-spect (s/and spect? conformy?))

(predicate-spec form?)
(defn form? [x]
  (and (sequential? x)
       (seq? x)
       (symbol? (first x))))

(defn spec-regex? [x]
  (and (map? x) (::s/op x)))

;; a thing that parse-spec will return a valid ::spect on
(s/def ::spect-like (s/or :spec s/spec? :spec-re spec-regex? :spect ::spect :key keyword? :sym symbol? :var var? :form form? :set set?))

(s/def ::valid-spect-like (s/or :spec s/spec? :spec-re spec-regex? :spect ::valid-spect :key keyword? :sym symbol? :var var? :form form? :set set?))

(s/fdef conform* :args (s/cat :spec spect? :x any?))

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
                (select-keys *a* [:file :line :column]))]
    (map->Invalid (merge args {:form form :a-loc a-loc :message message}))))

(extend-type Invalid
  Spect
  (conform* [this x]
    reject)
  Truthyness
  (truthyness [this]
    :ambiguous)
  WillAccept
  (will-accept- [this]
    reject))

(predicate-spec invoke?)
(defn invoke? [x]
  (satisfies? Invoke x))

(defn invoke [s args]
  {:pre [(validate! spect? s)
         (validate! spect? args)]
   :post [(validate! spect? %)]}
  (if (invoke? s)
    (invoke- s args)
    (invalid {:message (format "can't invoke %s" (print-str s))})))

(defn invoke-accept [s]
  {:pre [(validate! spect? s)]
   :post [(validate! spect? %)]}
  (if (invoke? s)
    (invoke-accept- s)
    (invalid {:message (format "can't invoke %s" (print-str s))})))

(s/fdef first-rest? :args (s/cat :x any?) :ret boolean?)
(defn first-rest? [x]
  (satisfies? FirstRest x))

(defn maybe-first* [ps]
  (if (first-rest? ps)
    (first- ps)
    (first ps)))

(defn maybe-rest* [ps]
  (if (first-rest? ps)
    (rest- ps)
    (rest ps)))

(defn second* [ps]
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
  (extend s FirstRest first-rest-singular-impl))

(declare reject)

(declare map->RegexAlt)

(extend-type Accept
  Spect
  (conform* [spec x]
    (when (and (accept? x) (= (:ret spec) (:ret x)))
      x))
  Regex
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
  WillAccept
  (will-accept- [this]
    reject))

(first-rest-singular Accept)

(extend-type Reject
  Spect
  (conform* [spec x]
    reject)
  Regex
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
  WillAccept
  (will-accept- [this]
    reject)
  Truthyness
  (truthyness [this]
    :falsey))

(first-rest-singular Reject)

(defrecord Unknown [form file line column])

(defn unknown? [x]
  (instance? Unknown x))

(s/fdef unknown :args (s/cat :args (s/keys :req-un [:invalid/message] :opt-un [:invalid/form])))
(defn unknown
  [{:keys [form a-loc message] :as args}]
  (let [a *a*
        form (if (find args form)
               form
               (:form *a*))
        a-loc (if (find args a-loc)
                a-loc
                (select-keys *a* [:file :line :column]))]
    (map->Unknown {:form form :a-loc a-loc :message message})))

(defn unknown-invoke [spec args]
  (unknown {:message (format "unknown-invoke: don't know how to invoke %s with %s" (print-str spec) (print-str args))}))

(extend-type Unknown
  Spect
  (conform* [this x]
    (when (unknown? x)
      x))
  Truthyness
  (truthyness [this]
    :ambiguous)
  WillAccept
  (will-accept- [this]
    this)
  Invoke
  (invoke- [spec args]
    (unknown-invoke spec args))
  (invoke-accept- [spec]
    (unknown {:message "invoke on unknown"}))
  FirstRest
  (first- [this]
    (unknown {:message "first on unknown"}))
  (rest- [this]
    (unknown {:message "rest on unknown"}))
  KeysGet
  (keys-get- [this k]
    (unknown {:message "get on unknown"})))

(defn known? [x]
  (not (unknown? x)))

(extend-type nil
  Regex
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
  Truthyness
  (truthyness [this]
    :falsey)
  FirstRest
  (first- [this]
    nil)
  (rest- [this]
    nil))

(extend-type Invalid
  Regex
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
    false))

(first-rest-singular Invalid)

(s/fdef spec-dx :args (s/cat :spec ::spect :x ::spect) :ret ::spect)
(defn spec-dx [spec x]
  (if (valid? spec x)
    (accept x)
    reject))

(extend-type Object
  Regex
  (return- [this]
    this)
  (regex? [this]
    false)
  (accept-nil? [this]
    false))

(def spect-regex-impl
  {:derivative spec-dx
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
             false)})

(defn extend-regex
  "extends the Regex protocol to a non-regex Spect"
  [s]
  (extend s Regex spect-regex-impl))

(defn will-accept-this
  "extend the spec to WillAccept itself"
  [s]
  (extend s WillAccept {:will-accept- (fn [this] this)}))

(extend-regex Unknown)

(defrecord RecurForm [args]
  Spect
  (conform* [this x]
    reject)
  Truthyness
  (truthyness [this]
    :ambiguous)
  WillAccept
  (will-accept- [this]
    reject))

(extend-regex RecurForm)

(defrecord ThrowForm [s]
  Spect
  (conform* [this x]
    reject)
  Truthyness
  (truthyness [this]
    :ambiguous)
  WillAccept
  (will-accept- [this]
    reject))

(extend-regex ThrowForm)

(s/fdef recur? :args (s/cat :x any?) :ret boolean?)
(defn recur? [x]
  (instance? RecurForm x))

(defn recur-form [args]
  (map->RecurForm {:args args}))

(s/fdef throwable? :args (s/cat :x any?) :ret boolean?)
(defn throwable? [x]
  (instance? Throwable x))

(s/fdef throw? :args (s/cat :x any?) :ret boolean?)
(defn throw? [x]
  (instance? ThrowForm x))

(s/fdef throw-form :args (s/cat :e spect?) :ret throw?)
(defn throw-form [e]
  (assert (spect? e))
  (map->ThrowForm {:s e}))

(s/fdef control-flow? :args (s/cat :x any?) :ret boolean?)
(defn control-flow? [x]
  (or (throw? x) (recur? x)))

(defn spect-or-control-flow? [x]
  (or (spect? x) (control-flow? x)))

(s/def ::dependent-specs (s/coll-of spect? :kind set?))

(defn dependent-specs* [s]
  {:post [(validate! ::dependent-specs %)]}
  (if (dependent-specs? s)
    (dependent-specs- s)
    #{}))

(s/fdef dependent-specs :args (s/cat :s (s/nilable spect?)) :ret ::dependent-specs)
(defn dependent-specs [s]
  (set/union (dependent-specs* s) (data/get-dependent-specs s)))

(s/fdef recursive-dependent-specs :args (s/cat :s (s/nilable spect?)) :ret ::dependent-specs)
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

(s/def ::class-or (s/or :c class-spec? :or or-spec?))
(s/fdef more-specfic-spec? :args (s/cat :a ::class-or :b ::class-or) :ret boolean?)

(defn more-specific-spec?
  [a b]
  (cond
    (or-spec? a) (every? (fn [a*]
                           (more-specific-spec? a* b)) (:ps a))
    (or-spec? b) (every? (fn [b*]
                           (more-specific-spec? a b*)) (:ps b))
    :else (do
            (when-not (and (class-spec? a) (class-spec? b))
              (println "more specific: a:" a "b:" b))
            (assert (class-spec? a))
            (assert (class-spec? b))
            (j/more-specific? (:cls a) (:cls b)))))

(defn most-specific-spec [specs]
  (reduce (fn [a b]
            (if (more-specific-spec? a b)
              a
              b)) (class-spec Object) specs))

(s/fdef maybe-alt- :args (s/cat :r1 (s/nilable spect?) :r2 (s/nilable spect?)) :ret spect?)
(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  {:post [(spect? %)]}
  (if (and r1 r2 (every? conformy? [r1 r2]))
    (map->RegexAlt {:ps [r1 r2]})
    (or (first (filter conformy? [r1 r2]))
        reject)))

(s/def :cat/ks (s/nilable (s/coll-of keyword?)))
(s/def :cat/ps (s/coll-of ::spect-like))
(s/def :cat/fs (s/nilable coll?))
(s/def :cat/ret (s/coll-of (s/or :s ::spect-like :cat :cat/ret) :kind vector?))

(defrecord RegexCat [ps ks forms ret])

(predicate-spec cat-spec?)
(defn cat-spec? [x]
  (instance? RegexCat x))

(s/fdef map->RegexCat :args (s/cat :x (s/keys :opt-un [:cat/ks :cat/ps :cat/fs] :req-un [:cat/ret])) :ret cat-spec?)

(declare new-regex-cat )

(s/fdef cat-spec :args (s/cat :m (s/map-of keyword? ::spect-like)) :ret cat-spec?)
(defn cat-spec [m]
  (new-regex-cat (vec (vals m)) nil nil []))

(s/fdef cat- :args (s/cat :ps (s/coll-of ::spect-like :kind sequential?)) :ret spect?)
(defn cat- [ps]
  (new-regex-cat ps nil nil []))

(s/fdef new-regex-cat :args (s/cat :ps (s/nilable (s/coll-of any?)) :ks (s/nilable (s/coll-of keyword?)) :fs (s/nilable coll?) :ret :cat/ret) :ret spect?)
(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
  (if (and ps
           (every? #(conformy? %) ps)
           (every? identity ps))
    (if (accept? p0)
      (let [ret-old ret
            _ (assert ret)
            ret (conj ret (:ret p0))]
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

(s/fdef cat-sequential :args (s/cat :c cat-spec?) :ret (s/cat :c cat-spec?))
(defn cat-sequential
  "Given a cat, return a new cat that will return a vector rather than map when conformed"
  [c]
  (new-regex-cat (:ps c) nil nil []))

(extend-type RegexCat
  Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  Regex
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
        (explain* pred path via in x))))
  (accept-nil? [this]
    (->>
      this
     :ps
     (map parse-spec)
     (every? accept-nil?)))
  (return- [{:keys [ps ks ret] :as this}]
    (return- (with-return (some-> ps first parse-spec) ret)))
  (with-return- [{:keys [ret] :as this} r]
    (let [ret (return- this)]
      (if (empty? ret)
        r
        (if r
          (conj r ret)
          (conj [] ret)))))
  (regex? [this]
    true)
  WillAccept
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
  FirstRest
  (first- [this]
    (let [p (some-> this :ps first parse-spec)]
      (if (and (first-rest? p) (regex? p))
        (first- p)
        p)))
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
  Compound
  (map- [this f]
    (->> this
         :ps
         (map parse-spec)
         (map f)))
  (filter- [this f]
    (->> this
         :ps
         (map parse-spec)
         (filter f)))
  (new- [this ps]
    (cat- (mapv parse-spec ps)))
  Truthyness
  (truthyness [this]
    :truthy))

(defrecord RegexSeq [ps ks forms splice ret])

(defn regex-seq? [x]
  (instance? RegexSeq x))

(s/def :seq/splice boolean?)

(s/fdef regex-seq :args (s/cat :s ::spect-like :opts (s/? (s/keys :opt-un [:seq/splice]))) :ret spect?)
(defn regex-seq [s & [{:keys [splice]}]]
  (if (conformy? s)
    (map->RegexSeq {:ps [s s]
                    :forms nil
                    :ret []
                    :splice splice})
    reject))

(defn new-regex-seq [ps ret splice forms]
  (assert (= 2 (count ps)))
  (let [[p1 p2] ps]
    (if (every? conformy? ps)
      (if (accept? p1)
        (map->RegexSeq {:ps [p2 p2]
                        :forms forms
                        :ret ((fnil conj []) ret (:ret p1))
                        :splice splice})
        (map->RegexSeq {:ps [p1 p2]
                        :forms forms
                        :ret ret
                        :splice splice}))
      reject)))

(extend-type RegexSeq
  Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  Regex
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
          ret (return- this)]
      (if (empty? ret)
        r
        ((if splice into conj) r ret))))
  (regex? [this]
    true)
  FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (let [x (will-accept this)]
      (if (and x (conformy? x))
        (let [ret (derivative this x)]
          (assert (or (spect? ret) (nil? ret)))
          ret)
        nil)))
  WillAccept
  (will-accept- [this]
    (let [[p1 p2] (map parse-spec (:ps this))]
      (if (accept-nil? p1)
        (or- [p1 p2])
        p1)))
  Truthyness
  (truthyness [this]
    :truthy)
  DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'seq?) (pred-spec #'seqable?) (class-spec clojure.lang.ISeq)}))

(s/fdef seq-of :args (s/cat :s ::spect-like) :ret spect?)
(defn seq-of [s]
  (regex-seq s))

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
          (let [ret (map->RegexAlt {:ps ps :ks ks :forms forms})]
            (if (nil? pr)
              (if k1
                (if (accept? p1)
                  p1
                  ret)
                p1)
              ret))
          reject))
      i)))

(defrecord RegexAlt [ps ks forms ret])

(defn alt? [x]
  (instance? RegexAlt x))

(defn alt- [ps]
  (new-regex-alt ps nil nil))

(defn ?- [x]
  (new-regex-alt [x (accept nil)] nil nil))

(extend-type RegexAlt
  Spect
  (conform* [spec data]
    (re-conform spec data))
  (explain* [spec path via in x]
    (re-explain spec path via in x))
  Regex
  (derivative [{:keys [ps ks forms] :as this} x]
    (let [ps (map parse-spec ps)]
      (new-regex-alt (mapv #(derivative % x) ps) ks forms)))

  (empty-regex [{:keys [ps ks forms] :as this}]
    (map->RegexAlt {:ps (map empty-regex ps)
                    :ks ks
                    :forms forms}))
  (accept-nil? [{:keys [ps ks forms] :as this}]
    (let [ps (map parse-spec ps)]
      (some accept-nil? ps)))
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
    (let [ret (return- this)]
      (if (= ret nil)
        r
        (conj r ret))))
  (re-explain* [{:keys [ps ks forms] :as spec} path via in x]
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
  (regex? [this]
    true)
  FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (let [x (will-accept this)]
      (if (and x (conformy? x))
        (derivative this x)
        nil)))
  WillAccept
  (will-accept- [this]
    (some->> this
             :ps
             (map parse-spec)
             (remove accept?)
             (mapv will-accept)
             or-))
  Truthyness
  (truthyness [this]
    (let [b (distinct (map truthyness (map parse-spec (:ps this))))]
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
  (and (seq? x) (symbol? (first x))))

(defn macro? [v]
  (and (var? v) (.isMacro v)))

(defn known-form? [x]
  (let [sym (first x)
        v (resolve sym)]
    (and (seq? x) (symbol? (first x)) (var? v) (can-parse? sym))))

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

(defn pred->value
  "If the spec is a pred that checks for a single value e.g. nil? false?, return the value, else nil"
  [s]
  (when (pred-spec? s)
    (condp = (:pred s)
      #'nil? (value nil)
      #'false? (value false)
      #'true? (value true)
      #'zero? (value 0)
      nil)))

(defrecord Value [v type])

(predicate-spec value?)
(defn value? [s]
  (instance? Value s))

(s/fdef value :args (s/cat :x any?) :ret value?)
(defn value
  "spec representing a single value"
  [v]
  (map->Value {:v v
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
  Spect
  (conform* [this x]
    (cond
      (instance? Value x) (when (= (:v this) (:v x))
                            x)
      (pred->value x) (when (= this (pred->value x))
                        x)
      :else (when (= (:v this) x)
              x)))
  Truthyness
  (truthyness [this]
    (if (:v this)
      :truthy
      :falsey))
  Invoke
  (invoke- [this args]
    (value-invoke this args))
  (invoke-accept- [this]
    (value-invoke-accept this))
  KeywordInvoke
  (keyword-invoke [this args]
    (let [key (first- args)
          else (second* args)
          rest (rest- (rest- args))]
      (cond
        (nil? key) (invalid {:message "not enough args"})
        rest (invalid {:message "value keyword invoke: too many args"})
        (and (value? key) (value? else)) (value (get (:v this) (:v key) (:v else)))
        (and (value? key) (nil? else)) (value (get (:v this) (:v key)))
        :else (unknown {:message "don't know how to keyword-invoke"}))))
  FirstRest
  (first- [{:keys [v] :as this}]
    (if (and v (or (seq? v) (seqable? v)))
      (if (seq v)
        (value (first v))
        nil)
      (invalid {:message (format "value %s does not support first" v)
                :form `(first ~v)})))
  (rest- [{:keys [v] :as this}]
    (if (or (seq? v) (seqable? v))
      (if (seq (rest v))
        (value (rest v))
        nil)
      (invalid {:message (format "value %s does not support rest" v) :form `(rest ~v)})))
  DependentSpecs
  (dependent-specs- [this]
    (if (nil? (:v this))
      #{}
      #{(class-spec (class (:v this)))}))
  WillAccept
  (will-accept- [this]
    this)
  KeysGet
  (keys-get- [{:keys [v] :as this} k]
    (if (coll? v)
      (value (get v k))
      (value nil))))

(extend-regex Value)

(predicate-spec raw-value?)
(defn raw-value?
  "A normal clojure value that isn't a spect, and isn't Value"
  [x]
  (not (spect? x)))

(s/fdef valuey? :args (s/cat :x any?) :ret boolean?)
(defn valuey? [x]
  (or (value? x) (raw-value? x)))

(s/def ::valuey (s/or :v value? :rv raw-value?))
(s/fdef get-value :args (s/cat :x ::valuey))
(defn get-value [x]
  (if (value? x)
    (:v x)
    x))

(predicate-spec truthy-value?)
(defn truthy-value? [s]
  "true if s is a value with a truthy value"
  (and (value? s) (boolean (:v s))))

  ;; 'container' spec, for when the user does e.g. (s/cat :x (s/spec
  ;; (s/* integer?)))  necessary because it changes the behavior of
  ;; `first`. Also useful as a `delay` for forward-declared specs

(defrecord SpecSpec [s])

(extend-type SpecSpec
  Spect
  (conform* [this x]
    (conform* (parse-spec (:s this)) x))
  WillAccept
  (will-accept- [this]
    (parse-spec (:s this)))
  Regex
  (derivative [this x]
    (derivative (parse-spec (:s this)) x))
  (empty-regex [this]
    (empty-regex (parse-spec (:s this))))
  (accept-nil? [this]
    (accept-nil? (parse-spec (:s this))))
  (return- [this]
    this)
  (with-return- [this ret]
    (with-return- (:s this) ret))
  (regex? [this]
    (-> this :s parse-spec regex?))
  FirstRest
  (first- [this]
    (-> this :s parse-spec first-))
  (rest- [this]
    (-> this :s parse-spec rest-))
  Truthyness
  (truthyness [this]
    (-> this :s parse-spec truthyness))
  Invoke
  (invoke- [this args]
    (-> this :s parse-spec (invoke args)))
  (invoke-accept- [this]
    (println "specspec invoke accept" (or
                                       (when (-> this :s s/spec?)
                                         (-> this :s s/form))
                                       (:s this)))
    (-> this :s parse-spec invoke-accept))
  DependentSpecs
  (dependent-specs- [this]
    (-> this :s parse-spec dependent-specs))
  SpecToClasses
  (spec->classes- [this]
    (-> this :s parse-spec spec->classes)))

(defn spec-spec? [x]
  (instance? SpecSpec x))

(defn spec-spec [s]
  (if (not (spec-spec? s))
    (map->SpecSpec {:s s})
    s))

(defrecord PredSpec [pred form])

(extend-regex PredSpec)
(first-rest-singular PredSpec)

(s/def ::pred (s/or :v var? :fn fn? :nil nil?))

(s/fdef pred-spec :args (s/cat :p ::pred) :ret ::spect)
(defn pred-spec [p]
  (map->PredSpec {:pred p
                  :form (when (var? p)
                          (var-name p))}))

(predicate-spec pred-spec?)
(defn pred-spec? [x]
  (instance? PredSpec x))

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
                 (and (or-spec? s)
                      (every? (fn [p]
                                (class-spec? p)) (:ps s))))))
   (most-specific-spec)
   (apply-map maybe-class)
   (set)))

(defn standard-spec->classes [s]
  (extend s SpecToClasses {:spec->classes- default-spec->classes}))

(defn pred-keyword-invoke [s args]
  (pred-spec #'any?))

(extend-type PredSpec
  Spect
  (conform* [spec x]
    (let [pred (:pred spec)]
      (cond
        (any-spec? spec) x
        (and (pred-spec? x) (= pred (:pred x))) x
        (and (= #'class? pred) (class-spec? x)) x

        ;; calling the pred should always be last resort
        ;; TODO remove this, or restrict to only using w/ pure functions. Not technically 'static' analysis.
        (and (conform-pred-args? spec (cat- [x])) (valuey? x)) (do
                                                                 (when (pred (get-value x))
                                                                   x)))))
  (explain* [spec path via in x]
    (when (not (valid? spec x))
      [{:path path :pred (:form spec) :val x :via via :in in}]))
  WillAccept
  (will-accept- [this]
    this)
  Truthyness
  (truthyness [this]
    (condp = (:pred this)
      #'boolean? :ambiguous
      #'false? :falsey
      #'nil? :falsey
      #'any? :ambiguous
      :truthy))
  Invoke
  (invoke- [this args]
    (let [pred (:pred this)]
      (cond
        (or (= #'keyword? pred) (= #'symbol? pred)) (pred-keyword-invoke this args)
        (= #'ifn? pred) (pred-spec #'any?)
        :else (invalid {:message (format "can't invoke %s" (print-str this))}))))
  (invoke-accept- [this]
    (let [pred (:pred this)]
      (cond
        (or (= #'keyword? pred) (= #'symbol? pred)) (cat- [(pred-spec #'any?) (?- (pred-spec #'any?))])
        (= #'ifn? pred) (pred-spec #'any?)
        :else (invalid {:message (format "can't invoke %s" (print-str this))})))))

;; Spec representing a java class. Probably won't need to use this
;; directly. Used in java interop, and other places where we don't
;; have 'real' specs

(defrecord ClassSpec [cls])

(defn maybe-map-equivalence-hack [c]
 ;;; hack for the godawful clojure.lang.MapEquivalence
;;; hack. deftype checks for MapEquivalence, an interface that is
;;; only implemented by APersistentMap, even though the defrecord
;;; constructor takes IPersistentMap.
  (if (= clojure.lang.MapEquivalence c)
    clojure.lang.APersistentMap
    c))

(s/fdef class-spec :args (s/cat :c class?) :ret spect?)
(defn class-spec [c]
  (assert (class? c) (format "not class?: %s %s" c (class c)))
  (map->ClassSpec {:cls c}))

(predicate-spec class-spec?)
(defn class-spec? [x]
  (instance? ClassSpec x))

(defn isa-boxed? [child parent]
  (or (isa? child parent)
      (and child parent (isa? (j/maybe-box child) (j/maybe-box parent)))))

(predicate-spec spec->classes?)
(defn spec->classes? [x]
  (satisfies? SpecToClasses x))

(s/def ::spec->classes (s/or :s class? :or-s (s/coll-of class? :kind set?)))
(s/fdef spec->classes :args (s/cat :s spect?) :ret ::spec->classes)
(defn spec->classes
  "Given a spec, return the set of concrete classes this spec could be.

   Because specs are more precise than class checks, casting to a class can destroy information. Using this anywhere other than java interop is a code smell."
  [spec]
  {:post [(validate! ::spec->classes %)]}
  (if (spec->classes? spec)
    (spec->classes- spec)
    (default-spec->classes spec)))

(extend-type ClassSpec
  Spect
  (conform* [this v]
    (let [{:keys [cls]} this
          v-classes (spec->classes v)]
      (or
       (when (= Object cls)
         v)
       (when (and (seq v-classes) (every? (fn [vc] (isa-boxed? vc cls)) v-classes))
         v))))
  WillAccept
  (will-accept- [this]
    this)
  Truthyness
  (truthyness [this]
    (condp = (:cls this)
      Boolean :ambiguous
      Object :ambiguous
      nil :falsey
      :truthy))
  DependentSpecs
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
  SpecToClasses
  (spec->classes- [this]
    (set [(:cls this)])))

(extend-regex ClassSpec)
(first-rest-singular ClassSpec)

;;type representing a value satisfying protocol p
(defrecord ProtocolSpec [p])

(defn protocol-spec? [x]
  (instance? ProtocolSpec x))

(extend-type ProtocolSpec
  Spect
  (conform* [this x]
    (cond
      (protocol-spec? x) (when (= (:p x) (:p this))
                           x)
      (value? x) (when (satisfies? (:p this) (:v x))
                   x)))
  WillAccept
  (will-accept- [this]
    this))

(s/fdef protocol- :args (s/cat :p protocol?) :ret spect?)
(defn protocol- [p]
  (map->ProtocolSpec {:p p}))

(defmethod parse-spec* :macro [x]
  (let [v (resolve (first x))
        args (rest x)
        form (apply v nil nil args)]
    (parse-spec* form)))

(defmethod parse-spec* :sym [x]
  (let [v (resolve x)]
    (if v
      (cond
        (var? v) (map->PredSpec {:pred v
                                 :form (symbol (str (.ns ^Var v)) (str (.sym ^Var v)))})
        (class? v) (map->ClassSpec {:cls v})
        :else (assert false (format "unknown: %s" x)))
      (value x))))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'clojure.core/fn [x]
  (if (= x any?-form)
    (pred-spec #'any?)
    (do
      (map->PredSpec {:pred nil ;;(eval x)
                      :form x}))))

(defmethod parse-spec* 'fn* [x]
  (if (= x any?-form)
    (pred-spec #'any?)
    (do
      (map->PredSpec {:pred nil ;;(eval x)
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
  (map->RegexCat {:ks (:ks x)
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
    (map->RegexCat {:ks ks
                    :ps ps
                    :forms ps
                    :ret []})))

(defmethod parse-spec* `s/cat-impl [x]
  (let [[ks ps forms] (rest x)
        forms (unquote-form forms)]
    (map->RegexCat {:ks ks
                    :ps forms
                    :ret []})))

(defmethod parse-spec* ::s/rep [x]
  (let [forms (if (vector? (:forms x))
                (:forms x)
                [(:forms x)])]
    (assert (= 1 (count forms)))
    (regex-seq (first forms) {:splice (:splice x)})))

(defmethod parse-spec* `s/rep-impl [x]
  (let [[form pred] (rest x)
        form (unquote-form form)]
    (regex-seq form {:splice false})))

(defmethod parse-spec* `s/+ [x]
  (let [forms (rest x)
        p (first forms)
        p (parse-spec p)]
    (assert (= 1 (count forms)))
    (map->RegexCat {:forms forms
                    :ps [p (regex-seq p {:splice true})]
                    :ret []})))

(defmethod parse-spec* `s/rep+impl [x]
  (let [[form pred] (rest x)
        form (unquote-form form)]
    (map->RegexCat {:forms [form]
                    :ps [form (regex-seq form {:splice true})]
                    :ret []})))

(defmethod parse-spec* `s/* [x]
  (let [forms (rest x)
        form (first forms)]
    (assert (= 1 (count forms)))
    (regex-seq form)))

(defmethod parse-spec* ::s/alt [x]
  (let [pairs (map vector (:ps x) (:forms x))]
    (map->RegexAlt {:ks (:ks x)
                    :forms (:forms x)
                    :ps (:forms x)})))

(defmethod parse-spec* `s/? [x]
  (map->RegexAlt {:ps [(second x) (accept nil)]}))

(defmethod parse-spec* `s/alt [x]
  (let [pairs (partition 2 (rest x))
        ks (mapv first pairs)
        forms (mapv second pairs)]
    (map->RegexAlt {:ks ks
                    :forms forms
                    :ps forms})))

(defmethod parse-spec* `s/alt-impl [x]
  (let [[ks ps forms] (rest x)]
    (map->RegexAlt {:ks ks
                    :forms forms
                    :ps (unquote-form forms)})))

(defmethod parse-spec* `s/maybe-impl [x]
  (let [[pred form] (rest x)
        form (unquote-form form)]
    (map->RegexAlt {:ps [form (accept nil)]})))

(defmethod parse-spec* :clojure.spec.alpha/amp [x]
  (unknown {:message (format "TODO don't know how to handle %s" x)}))

(defmethod parse-spec* `s/amp-impl [x]
  (unknown {:message (format "TODO don't know how to handle %s" x)}))

(defrecord NotSpec [s])

(s/fdef not- :args (s/cat :s spect?) :ret spect?)
(defn not- [s]
  (map->NotSpec {:s s}))

(defn not-spec? [x]
  (instance? NotSpec x))

(extend-type NotSpec
  Spect
  (conform* [this x]
    (if (and (not (conformy? (conform* (:s this) x)))
             (not (conformy? (conform* x (:s this)))))
      x
      (invalid {:message (format "%s does not conform to %s" (print-str x) (print-str this))})))
  WillAccept
  (will-accept- [this]
    this)
  Truthyness
  (truthyness [this]
    (let [t (truthyness (:s this))]
      (condp = t
        :ambiguous :ambiguous
        :truthy :falsey
        :falsey :truthy))))

(extend-regex NotSpec)

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:ps and-s))
    x))

(defrecord AndSpec [ps])

(predicate-spec and-spec?)
(defn and-spec? [x]
  (instance? AndSpec x))

(s/fdef and-classes-compatible? :args (s/cat :ps (s/coll-of ::spect-like)) :ret boolean?)
(defn and-classes-compatible?
  "True if the `and` pred java classes are incompatible (concrete classes that aren't ancestors)"
  [ps]
  (let [compatible? (fn [a b]
                      {:pre [(class? a) (class? b)]}
                      (or (j/interface? a)
                          (j/interface? b)
                          (isa? a b)
                          (isa? b a)))
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
  "True if ps contains X and not X"
  [ps]
  (let [nots (filter not-spec? ps)
        not-preds (set (map :s nots))]
    (some (fn [p]
            (some (fn [np]
                    (valid? np p)) not-preds)) ps)))

(defn and-value-contradiction?
  "true if and ps contains two non-equal values"
  [ps]
  (let [values (filter value? ps)]
    (if (seq values)
      (not (apply = (map :v values)))
      false)))

(s/fdef and- :args (s/cat :forms (s/coll-of ::spect-like)) :ret spect?)
(defn and- [ps]
  (let [ps (mapcat (fn [p] (if (and-spec? p)
                             (:ps p)
                             [p])) ps)
        ps (distinct ps)]
    (cond
      (not (and-classes-compatible? ps)) (invalid {:message "and contains incompatible java classes"})
      (and-not-contradiction? ps) (invalid {:message "and- contains contradictions"})
      (and-value-contradiction? ps) (invalid {:message "and- contains incompatible values"})
      (>= (count ps) 2) (map->AndSpec {:ps ps})
      :else (first ps))))

(s/fdef and-conj :args (s/cat :s spect? :x spect?) :ret spect?)
(defn and-conj
  [s x]
  (and- (conj (:ps s) x)))

(defn equivalent? [s1 s2]
  (and (valid? s1 s2)
       (valid? s2 s1)))

(s/fdef add-constraint :args (s/cat :a spect? :b spect?) :ret spect?)
(defn add-constraint
  "Given a spec s, update it to also conform to spec `constraint`"
  [s constraint]
  {:pre [(spect? s) (spect? constraint)]
   :post [(spect? %)]}
  (cond
    (value? s) (if (valid? constraint s)
                 s ;; can't make values more specific
                 (invalid {:message (format "can't add constraint %s to %s" (print-str constraint) (print-str s))}))

    (equivalent? (pred-spec #'any?) constraint) s
    (equivalent? (class-spec Object) constraint) s

    (equivalent? (pred-spec #'any?) s) constraint
    (equivalent? (class-spec Object) s) constraint

    (and-spec? s) (and-conj s constraint)
    :else (and- [s constraint])))

(s/fdef add-or-constraint :args (s/cat :s spect? :constraint spect?) :ret spect?)
(defn add-or-constraint
  "given a spec s, `or` it with constraint"
  [s constraint]
  (or- [s constraint]))

(s/fdef non-contradiction? :args (s/cat :s spect? :constraint spect?) :ret boolean?)
(defn non-contradiction?
  "True if adding constraint to s won't result in contradiction"
  [s constraint]
  (conformy? (add-constraint s constraint)))

(extend-type AndSpec
  Spect
  (conform* [this x]
    (conform this x))
  DependentSpecs
  (dependent-specs- [spec]
    (->> spec
         :ps
         (map parse-spec)
         (map dependent-specs)
         (apply set/union)))
  WillAccept
  (will-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (and-)))
  Truthyness
  (truthyness [this]
    (let [b (distinct (->> this :ps (map parse-spec) (map truthyness)))]
      (if (= 1 (count b))
        (first b)
        :ambiguous)))
  FirstRest
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
  Compound
  (map- [spec f]
    (->> spec
         :ps
         (map parse-spec)
         (map f)))
  (filter- [spec f]
    (->> spec
         :ps
         (map parse-spec)
         (filter f)))
  (new- [this ps]
    (and- (map parse-spec ps)))
  KeysGet
  (keys-get- [this k]
    (->> this
         :ps
         (map parse-spec)
         (map (fn [p]
                (keys-get p k)))
         (filter identity)
         (first))))

(extend-regex AndSpec)

(defmethod parse-spec* `s/and [x]
  (and- (rest x)))

(defmethod parse-spec* `s/and-spec-impl [x]
  (let [[forms preds gen-fn] (rest x)
        ps (unquote-form forms)]
    (and- ps)))

(defrecord OrSpec [ps ks])

(predicate-spec or-spec?)
(defn or-spec? [x]
  (instance? OrSpec x))

(s/def :or/ps (s/coll-of ::spect-like :kind set?))

(s/fdef map->OrSpec :args (s/cat :m (s/keys :req-un [:or/ps])) :ret or-spec?)

(s/def ::or-args (s/coll-of (s/nilable ::spect-like)))
(s/def ::or-ret (s/nilable spect?))
(s/fdef or- :args (s/cat :ps ::or-args) :ret ::or-ret)
(defn or- [ps]
  {:pre [(validate! ::or-args ps)]
   :post [(validate! ::or-ret %)]}
  (let [or-ps (mapcat (fn [p] (when (or-spec? p)
                                (:ps p))) ps)
        ps (remove or-spec? ps)
        ps (concat ps or-ps)
        ps (set ps)]
    (cond
      (some invalid? ps) (invalid {:message "or invalid"
                                   :causes (filter invalid? ps)})
      (some reject? ps) reject
      (>= (count ps) 2) (map->OrSpec {:ps ps})
      (= 1 (count ps)) (first ps)
      :else (do
              (assert false)
              (invalid {:message "or spect requires at least one arg"})))))

(s/fdef or-conj :args (s/cat :s spect? :x spect?) :ret spect?)
(defn or-conj [s x]
  (if (or-spec? x)
    (or- (conj (:ps s) x))
    (or- [s x])))

(extend-type OrSpec
  Spect
  (conform* [this x]
    (->>
     (:ps this)
     (map parse-spec)
     (some (fn [p]
             (when (valid? p x)
               x)))))
  DependentSpecs
  (dependent-specs- [this]
    (->> (:ps this)
         (map parse-spec)
         (map dependent-specs)
         (apply set/intersection)))
  WillAccept
  (will-accept- [this]
    (->> this :ps (map parse-spec) (mapv will-accept) (or-)))
  Truthyness
  (truthyness [this]
    (let [b (->> this :ps (map parse-spec) (map truthyness) distinct)]
      (if (= 1 (count b))
        (first b)
        :ambiguous)))
  FirstRest
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
  Compound
  (map- [this f]
    (let [kps (->> (mapv vector (or (:ks this) (repeat nil)) (:ps this))
                   (map (fn [[k p]]
                          [k (f (parse-spec p))])))]
      (map second kps)))
  (filter- [this f]
    (->> this
         :ps
         (map parse-spec)
         (filter f)))
  (new- [this ps]
    (or- ps))
  Invoke
  (invoke- [this args]
    (->> this
         :ps
         (map parse-spec)
         (map (fn [p]
                (invoke p args)))
         (or-)))
  (invoke-accept- [this]
    (->> this
         :ps
         (map parse-spec)
         (map invoke-accept)
         (or-)))
  KeywordInvoke
  (keyword-invoke [this args]
    (->> (:ps this)
         (map parse-spec)
         (filter keyword-invoke?)
         (map (fn [p]
                (keyword-invoke p args)))
         (distinct)
         (or-)))
  KeysGet
  (keys-get- [this k]
    (->> this
         :ps
         (mapv parse-spec)
         (mapv (fn [p] (keys-get p k)))
         (distinct)
         (or-)))
  Regex
  (regex? [this]
    (->> this
         :ps
         (map parse-spec)
         (some regex?)))
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
         (some accept-nil?)))
  (return- [this]
    this
    ;; (->> this
    ;;      :ps
    ;;      (map parse-spec)
    ;;      (filter accept-nil?)
    ;;      (map return)
    ;;      (or-))
    )
  (with-return- [this x]
    (->> this
         :ps
         (map parse-spec)
         (mapcat (fn [p]
                   (with-return p x)))
         ((fn [ps]
            (if (seq ps)
              (or- ps)
              x)))))
  SpecToClasses
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

(declare maybe-or-disj)

(s/fdef or-disj :args (s/cat :s or-spec? :p spect?) :ret spect?)
(defn or-disj
  "Remove pred from the set of preds"
  [s pred]
  (->> s
       (map* parse-spec)
       (map (fn [p]
               (maybe-or-disj p pred)))
       (filter (fn [p]
                 (not (equivalent? p pred))))
       (or-)))

(defn maybe-or-disj
  [s pred]
  (if (or-spec? s)
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

(defrecord TupleSpec [ps])

(defn tuple-spec [ps]
  (map->TupleSpec {:ps ps}))

(extend-type TupleSpec
  Spect
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
  Regex
  (accept-nil? [this]
    (not (seq (:ps this))))
  FirstRest
  (first- [this]
    (some-> this :ps first parse-spec))
  (rest- [this]
    (when-let [r (-> this :ps rest seq)]
      (tuple-spec r))))

(extend-regex TupleSpec)

(defmethod parse-spec* `s/tuple [x]
  (let [preds (rest x)]
    (map->TupleSpec {:ps (vec preds)})))

(defmethod parse-spec* `s/tuple-impl [x]
  (let [[forms preds] (rest x)]
    (map->TupleSpec {:ps (unquote-form forms)})))

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

(defrecord KeysSpec [req req-un opt opt-un])

(predicate-spec keys-spec?)
(defn keys-spec? [x]
  (instance? KeysSpec x))

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
               (explain* spec (conj path key) via in val)))))))

(s/def ::keys-spec keys-spec?)

(s/fdef keys-spec :args (s/cat :req (s/nilable (s/map-of qualified-keyword? ::spect-like))
                               :req-un (s/nilable (s/map-of keyword? ::spect-like))
                               :opt (s/nilable (s/map-of qualified-keyword? ::spect-like))
                               :opt-un (s/nilable (s/map-of keyword? ::spect-like)))
        :ret keys-spec?)

(defn keys-spec [req req-un opt opt-un]
  (map->KeysSpec {:req req
                  :req-un (into {} (map (fn [[k s]]
                                          [(strip-namespace k) s]) req-un))
                  :opt opt
                  :opt-un (into {} (map (fn [[k s]]
                                          [(strip-namespace k) s]) opt-un))}))

(extend-type KeysSpec
  WillAccept
  (will-accept- [this]
    this)
  DependentSpecs
  (dependent-specs- [this]
    #{(class-spec clojure.lang.PersistentHashMap) (pred-spec #'map?) (pred-spec #'coll?)})
  Truthyness
  (truthyness [this]
    :truthy)
  KeywordInvoke
  (keyword-invoke [this args]
    (let [k (first- args)
          else (second* args)
          rest (rest- (rest- args))]
      (cond
        rest (invalid {:message (format "keysspec keywordw invoke: too many args:" (print-str this) (print-str args))})
        else (keyspec-get-key this k else)
        k (keyspec-get-key this k)
        :else (invalid {:message "not enough args"}))))
  KeysGet
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
  Spect
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

(defrecord CollOfSpec [s kind])

(extend-regex CollOfSpec)
(will-accept-this CollOfSpec)

(s/fdef coll-of :args (s/cat :s ::spect-like :kind (s/? (s/nilable coll?))) :ret ::spect)
(defn coll-of
  ([s]
   (coll-of s nil))
  ([s kind]
   (map->CollOfSpec {:s s
                     :kind kind})))

(predicate-spec coll-of?)
(defn coll-of? [x]
  (instance? CollOfSpec x))

(s/fdef infinite? :args (s/cat :r first-rest?) :ret boolean?)
(defn infinite?
  "True if this spec accepts infinite input"
  [r]
  (or (regex-seq? r)
      (coll-of? r)
      (unknown? r)
      (if-let [n (some-> r :ps first)]
        (recur n)
        false)))

(s/fdef coll-items :args (s/cat :s spect?) :ret (s/coll-of spect? :kind set?))
(defn coll-items
  "The set of all items in a regex/coll spec"
  [s]
  {:post [(validate! (s/coll-of spect? :kind set?) %)]}
  (loop [ret #{}
         s s]
    (let [v (first- s)]
      (if (conformy? v)
        (let [ret (conj ret v)]
          (if (and (not (infinite? s)) (rest- s))
            (recur ret (rest- s))
            ret))
        ret))))

(s/fdef will-accept-concrete :args (s/cat :s spect?) :ret (s/* spect?))
(defn will-accept-concrete
  "will-accept, but recursively resolve or/alt specs, returns a seq of spects"
  [s]
  (->> s
       (will-accept)
       ((fn [x]
          (cond
            (or (or-spec? x) (alt? x)) (->> x :ps (map parse-spec) (mapcat will-accept-concrete))
            :else [x])))))

(s/fdef all-possible-values* :args (s/cat :q (s/and queue? (s/coll-of spect?)) :seen (s/coll-of spect? :kind set?)) :ret (s/coll-of spect?))
(defn all-possible-values* [[s & sr] seen]
  ;;{:post [(do (println "all-possible-values*" s seen "=>" %) true)]}
  (if (and s (not (contains? seen s)))
    (let [new-specs (->> s
                         (will-accept-concrete)
                         (map (fn [x]
                                {:pre [(spect? s)]}
                                (derivative s x)))
                         (remove reject?)
                         (remove nil?)
                         (remove (fn [s]
                                   (contains? seen s)))
                         doall)
          ret (filter (fn [s]
                        (or (accept? s)
                            (accept-nil? s))) new-specs)
          new-q (remove (fn [s]
                          (accept? s)) new-specs)]
      (lazy-cat (map return ret) (all-possible-values* (queue (distinct (concat sr new-q))) (conj seen s))))
    []))

(s/fdef all-possible-values :args (s/cat :s spect?) :ret (s/coll-of spect?))
(defn all-possible-values
  "Given a regex spec, return a sample of the possible concrete specs"
  [spec]
  {:pre [(do (when-not (spect? spec) (println "all-possible:" spec)) true) (spect? spec)]}
  (take 50 (all-possible-values* (queue [spec]) #{})))

(s/fdef conform-collof-value :args (s/cat :collof ::spect :x (s/nilable value?)))
(defn conform-collof-value [collof x]
  (let [s (parse-spec (:s collof))
        v (get-value x)]
    (when (and (or (nil? (:kind collof))
                   (and (:empty-kind collof)
                        (= (:empty-kind collof)
                           (empty v)))
                   (empty? v))
               (or (and (value? x)
                        (let [v (get-value x)]
                          (and (sequential? v)
                               (not (seq v)))))
                   (every? (fn [v]
                          (valid? s v)) (all-possible-values x))))
      x)))

(s/fdef coll-of-key :args (s/cat :s spect?) :ret #{:map :set :vector :unknown})
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
        else (or (second* args) (value nil))
        rest (rest- (rest- args))
        map-key-spec (-> s :s parse-spec first-)
        map-val-spec (-> s :s parse-spec second*)]
    (cond
      rest (invalid {:message (format "too many args to invoke, got %s" (print-str args))})
      (not key) (invalid {:message "not enough args to invoke"})
      (valid? map-key-spec key) (or- [map-val-spec else])
      (or-spec? key) (if (or-some #(valid? map-key-spec %) key)
                       (or- [map-val-spec else])
                       (value nil))
      :else (if else
              else
              (value nil)))))

(extend-type CollOfSpec
  Spect
  (conform* [this x]
    (cond
      (instance? CollOfSpec x) (when (valid? (parse-spec (:s this)) (parse-spec (:s x)))
                                 x)
      (value? x) (conform-collof-value this x)))
  FirstRest
  (first- [this]
    (parse-spec (:s this)))
  (rest- [this]
    this)
  Truthyness
  (truthyness [this]
    :truthy)
  Invoke
  (invoke- [this args]
    (coll-of-invoke this args))
  DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'seqable?) (class-spec (or (class (:s this)) clojure.lang.PersistentList))})
  SpecToClasses
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
    (map->CollOfSpec (merge {:s s
                             :empty-kind empty-kind} opts))))

(defrecord ArrayOf [p]
  Spect
  (conform* [this x]
    (when (and (instance? ArrayOf x) (valid? (parse-spec p) (parse-spec (:p x))))
      x))
  Truthyness
  (truthyness [this]
    :truthy)
  WillAccept
  (will-accept- [this]
    this))

(first-rest-singular ArrayOf)
(extend-regex ArrayOf)

(s/fdef array-of :args (s/cat :x class-spec?) :ret spect?)
(defn array-of [p]
  (map->ArrayOf {:p p}))

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
       (map->KeysSpec)))

(defn coll-of-map? [s]
  (and (coll-of? s) (= map? (:kind s))))

(declare merge-specs)
(s/fdef merge-or-keys :args (s/cat :or or-spec? :key keys-spec?) :ret or-spec?)
(defn merge-or-keys [o k]
  (or- (mapv (fn [p]
               (merge-specs p k)) (:ps o))))

(defn merge-specs [& specs]
  (reduce (fn [s1 s2]
            (let [s1 (parse-spec s1)
                  s2 (parse-spec s2)]
              (cond
                (and (keys-spec? s1) (keys-spec? s2)) (merge-keys [s1 s2])
                (and (or-spec? s1) (keys-spec? s2)) (merge-or-keys s1 s2)
                (and (keys-spec? s1) (or-spec? s2)) (merge-or-keys s2 s1)
                :else (and- [s1 s2])))) specs))

(s/fdef conform-map-of :args (s/cat :m ::spect :v value?) :ret any?)
(defn conform-map-of [map-of v]
  (when (and (every? (fn [k]
                       (valid? (:ks map-of) k)) (keys (:v v)))
             (every? (fn [v]
                       (valid? (:vs map-of) v)) (vals (:v v))))
    v))

(defrecord MapOf [ks vs])

(extend-type MapOf
  Spect
  (conform* [{:keys [ks vs] :as this} x]
    (cond
      (instance? MapOf x) (when (and (valid? (parse-spec ks) (parse-spec (:ks x)))
                                     (valid? (parse-spec vs) (parse-spec (:vs x))))
                            x)
      (value? x) (conform-map-of this x)
      :else nil))
  DependentSpecs
  (dependent-specs- [s]
    #{(class-spec clojure.lang.PersistentHashMap)})
  Truthyness
  (truthyness [this]
    :truthy)
  Invoke
  (invoke- [{:keys [ks vs] :as this} args]
    (assert (cat-spec? args))
    (let [arg-count (count (:ps args))
          k (first- args)
          else (or (second* args) (value nil))]
      (if (contains? #{1 2} arg-count)
        (if (apply-some (fn [k s]
                          (valid? s k)) k (parse-spec ks))
          (or- [(parse-spec vs) else])
          else)
        (invalid {:message (format "wrong number of args passed to %s, got %s" (print-str this) (print-str args))})))))

(extend-regex MapOf)
(will-accept-this MapOf)

(defn map-of [key-pred val-pred]
  (map->MapOf {:ks key-pred
               :vs val-pred}))

(defn parse-map-of [x]
  (let [[form pred opts] (rest x)
        tuple (unquote-form form)
        [_ k v] tuple]
    (map->MapOf {:ks (parse-spec k)
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
      (map->CollOfSpec (merge {:s s
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

(defrecord FnSpec [args ret fn var])

(extend-regex FnSpec)
(will-accept-this FnSpec)

(predicate-spec fn-spec?)
(defn fn-spec? [x]
  (instance? FnSpec x))

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
      (invalid {:message (format "invalid fn: %s" (print-str (into {} invalid-args)))})
      (map->FnSpec {:args args
                    :ret ret
                    :fn f}))))

(s/fdef get-var-spec :args (s/cat :v var?) :ret (s/nilable spect?))
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
      (and (-> s :args cat-spec?)
           (-> s :args :ps count (= 1))
           (-> s :ret (= (pred-spec #'boolean?)))
           (var-named-predicate? v))
      false)))

(def var-predicate? (memo/memo var-predicate?-))

(defn valid-transformation?
  "True if a spec transformer can transform from A->B"
  [a b]
  (or (valid? a b) (invalid? b) (unknown? b)))

(s/fdef maybe-transform :args (s/cat :s spect? :args spect?) :ret spect?)
(defn maybe-transform [spec args]
  {:post [(do (when-not (spect? %)
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

(s/fdef invoke-fn-spec :args (s/cat :s fn-spec? :args spect?) :ret spect?)
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
            (invalid {:message (format "can't invoke %s (%s) with %s" v (print-str spec) (print-str invoke-args))})
            (invalid {:message (format "invoke with invalid args %s" (print-str invoke-args))}))
          (unknown {:message (format "invoke %s w/ unknown args %s" v (print-str invoke-args))})))
      (unknown {:message (format "invoke %s no :args spec" spec)}))))

(extend-type FnSpec
  Spect
  (conform* [this x]
    (when (and (instance? FnSpec x)
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
  DependentSpecs
  (dependent-specs- [this]
    #{(pred-spec #'fn?) (pred-spec #'ifn?)})
  Invoke
  (invoke- [this args]
    (invoke-fn-spec this args))
  (invoke-accept- [this]
    (if (:args this)
      (:args this)
      (unknown {:message (format "no :args spec on %s" this)})))
  Truthyness
  (truthyness [this]
    :truthy))

(defmethod parse-spec* `s/fspec [x]
  (let [pairs (->> x rest (partition 2))
        pairs (map (fn [[k p]]
                     (when p
                       [k (parse-spec p)])) pairs)
        args (into {} pairs)]
    (map->FnSpec args)))

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
    (map->FnSpec (merge (when arg-spec
                          {:args args})
                        (when ret-spec
                          {:ret ret})
                        (when fn-spec
                          {:fn fn})))))

(defn maybe-resolve-keyword-spec [x]
  (if (and (value? x) (keyword? (:v x)) (#'s/maybe-spec (:v x)))
    (parse-spec (s/spec (:v x)))
    x))

(s/fdef valid-invoke? :args (s/cat :s spect? :args ::spect) :ret boolean?)
(defn valid-invoke?
  "check that fnspec can be invoked w/ args"
  [spec args]
  (cond
    (unknown? spec) spec
    (fn-spec? spec) (valid? (:args spec) args)
    :else (invalid {:message (format "can't invoke %s" (print-str spec))})))

(s/fdef conform-pred-args? :args (s/cat :p pred-spec? :x spect?) :ret boolean?)
(defn conform-pred-args?
  [pred-spec args-spect]
  (if-let [fn-spec (resolve-pred-spec pred-spec)]
    (valid-invoke? fn-spec args-spect)
    false))

(defrecord MultiSpec [multimethod retag])

(defn multispec [method retag]
  (map->MultiSpec {:multimethod method
                   :retag retag}))

(predicate-spec multispec?)
(defn multispec? [x]
  (instance? MultiSpec x))

(s/fdef multispec-dispatch-ret-value :args (s/cat :ms multispec? :val any?) :ret spect?)
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

(s/fdef multispec-dispatch-ret-value :args (s/cat :ms multispec? :val spect?) :ret spect?)
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
  Spect
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
  DependentSpecs
  (dependent-specs- [this]
    (dependent-specs- (multispec-default-spec this)))
  KeywordInvoke
  (keyword-invoke [this k]
    (keyword-invoke (multispec-default-spec this) k))
  WillAccept
  (will-accept- [this]
    (->>
     @(:multimethod this)
     (multimethod-dispatch-values)
     (map parse-spec)
     (mapv (fn [v]
            (multispec-dispatch-ret-value this v)))
     or-))
  Truthyness
  (truthyness [this]
    (truthyness (multispec-default-spec this))))

(extend-regex MultiSpec)

(defn maybe-spec-spec [x]
  (if (regex-seq? x)
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

(extend-protocol Spect
  clojure.spec.alpha.Spec
  (conform* [spec x]
    (conform* (parse-spec spec) (parse-spec x))))

(extend-type clojure.spec.alpha.Spec
  Spect
  (conform* [spec x]
    (conform* (parse-spec* spec) x)))

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
        (re-explain* spec path via (conj in i) data)))))

(s/fdef value-invoke-dispatch :args (s/cat :f spect? :args spect?) :ret keyword?)
(defn value-invoke-dispatch [f args]
  (assert (first-rest? args))
  (let [val f
        obj (first- args)
        else (second* args)
        rest (rest- (rest- args))]
    (assert (value? val))
    (cond
      (var? (:v f)) :var
      (fn? (:v f)) :fn
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
        else (second* args)]
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
        else (second* args)
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
      (keyword? v) (or- [(cat- [v (pred-spec #'any?)]) (cat- [v (pred-spec #'any?) (pred-spec #'any?)])])
      (nil? v) (invalid {:message "can't invoke nil"})
      :else (do
              (println "unknown value-invoke:" v*)
              (assert false (format "unknown value invoke: %s" v))))))

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
      (and spec-or args-and) :or-and
      spec-and :spec-and
      args-and :args-and
      args-or :args-or
      :else :simple)))

(defmulti conform-compound #'conform-strategy)

(defmethod conform-compound :and-and [spec args]
  (when (every? (fn [p]
                  (valid? p args)) (map parse-spec (:ps spec)))
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
  {:post [(do (when-not (s/valid? (:ret (s/get-spec #'conform*)) %) (println "conform* invalid:" spec args "=>" %)) true) (s/valid? (:ret (s/get-spec #'conform*)) %)]}
  (conform* spec args))

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


(s/fdef conform- :args (s/cat :s ::spect :args (s/nilable (s/and spect? map?))) :ret ::spect)
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

(defn conform-destructure
  "Given args that conform to spec, return the smallest part of the spec that conforms. (conform-destructure (and- [x y (not z)]) y) => y"
  [spec args]
  (if (valid? args spec)
    (filter* (fn [s] (valid? args s)) spec)
    nil))

(def ^:dynamic *conform-cache* false)

(def conform (if *conform-cache*
               (memo/lru conform- :lru/threshold 10000)
               conform-))

(s/fdef valid? :args (s/cat :s ::spect :args (s/nilable spect?)) :ret boolean?)
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
  (explain* spec [] [] [] x))

(defn explain-out [data])

(defn explain [spec args]
  (explain-data spec args))

(defmethod print-method Unknown [spec ^Writer w]
  (let [{:keys [file line column]} spec]
    (.write w (str "#Unknown[" (if (seq (:message spec))
                                 (:message spec)
                                 (print-method (:form spec) w))
                   (when file
                     (str file line column)) "]"))))

(defn regex-print-method [re-name spec ^Writer w]
  (.write w (str "#" re-name ))
  (print-method (:ps spec) w))

(defmethod print-method RegexCat [v ^Writer w]
  (regex-print-method "Cat" v w))

(defmethod print-method RegexSeq [v ^Writer w]
  (regex-print-method "Seq" v w))

(defmethod print-method RegexAlt [v ^Writer w]
  (regex-print-method "Alt" v w))

(defmethod print-method Value [v ^Writer w]
  (.write w "#Value[")
  (print-method (:v v) w)
  (.write w "]"))

(defmethod print-method PredSpec [v ^Writer w]
  (.write w (format "#Pred[" ))
  (print-method (:form v) w)
  (.write w "]"))

(defmethod print-method ClassSpec [v ^Writer w]
  (.write w "#Class[")
  (print-method (:cls v) w)
  (.write w "]"))

(defmethod print-method AndSpec [v ^Writer w]
  (.write w "#And")
  (print-method (:ps v) w))

(defmethod print-method OrSpec [v ^Writer w]
  (.write w (format "#Or"))
  (#'clojure.core/print-sequential "[" print-method " " "]" (:ps v) w))

(defmethod print-method FnSpec [s ^Writer w]
  (.write w "#Fn")
  (->> (map #(find s %) [:var :args :ret :fn])
       (filter (fn [[k v]]
                 (identity v)))
       (apply concat)
       (vec)
       (#(print-method % w))))

(defmethod print-method KeysSpec [spec ^Writer w]
  (.write w "#Keys{")
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
    (.write w "#CollOf")
    (#'clojure.core/print-sequential open print-method " " close [(:s spec)] w)))
