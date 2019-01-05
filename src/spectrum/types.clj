(ns spectrum.types
  (:refer-clojure :exclude [vector-of * +])
  (:require [clojure.spec.alpha :as s]
            [spectrum.java :as j]
            [spectrum.util :refer [instrument-ns]]))

(def ignore? (partial = '_))

(defn logic? [x]
  (or (and (symbol? x) (= \? (-> x name first)))
      (ignore? x)))

(s/def ::type-atom (s/or :lvar logic? :v var? :s symbol?))

(defn tagged? [t]
  (and (vector? t)
       (-> t first symbol?)
       (not (logic? (first t)))))

(s/def ::type (s/or :ta ::type-atom :tagged-type tagged? :n nil?))
(s/def ::types (s/coll-of ::type))

(defn type-tag [t]
  (when (and (vector? t) (symbol? (first t)))
    (nth t 0)))

(defn tagged-type? [name x]
  (and (vector? x)
       (= name (first x))))

(defmacro defn-type-pred [name tag]
  `(defn ~name [x#]
     (tagged-type? ~tag x#)))

(defmacro defn-tagged-type
  "defn ~name as a fn that constructs a vector tagged type"
  [name tag]
  `(defn ~name [& args#]
     (apply conj [~tag] args#)))

(defn-type-pred class-t? 'class)

(defn-tagged-type accept-t 'accept)
(defn-type-pred accept-t? 'accept)
(defn-tagged-type invalid 'invalid)
(defn-type-pred invalid? 'invalid)

(defn-tagged-type value-t 'value)
(defn-type-pred value-t? 'value)

(defn-tagged-type throw-t 'throw)
(defn-tagged-type recur-t 'recur)

(defn-tagged-type protocol-t 'protocol)

(defn-type-pred and-t? 'and)
(defn-type-pred or-t? 'or)
(defn-type-pred not-t? 'not)

(defn-tagged-type not-t 'not)

(declare cat-t)
(defn-type-pred cat-t? 'cat)
(defn-type-pred alt-t? 'alt)

(defn-tagged-type seq-of 'seq-of)
(defn-type-pred seq-t? 'seq-of)

(defn-tagged-type maybe-t 'maybe)
(defn-type-pred maybe-t? 'maybe)

(s/fdef map-entry :args (s/cat :x ::type :y ::type) :ret ::type)
(defn-tagged-type map-entry 'map-entry)

(defn-tagged-type map-of 'map-of)

(defn-tagged-type coll-of 'coll-of)

(s/fdef vector-of :args (s/cat :x ::type) :ret ::type)
(defn-tagged-type vector-of 'vector-of)

(s/def :keys/key-class (s/map-of keyword? ::type))

(s/def :keys/req :keys/key-class)
(s/def :keys/req-un :keys/key-class)
(s/def :keys/opt :keys/key-class)
(s/def :keys/opt-un :keys/key-class)
(s/fdef keys-t :args (s/cat :k (s/keys :opt-un [:keys/req :keys/req-un :keys/opt :keys/opt-un])))
(defn-tagged-type keys-t 'keys)

(s/def :fn/args (s/coll-of ::type :kind vector?))
(s/def :fn/ret ::type)
(s/def ::fn-args (s/map-of :fn/args :fn/ret))
(s/def ::fn-tag #{'fn})
(s/def ::fn-t (s/tuple ::fn-tag ::fn-args))

;; fns are maps of arguments to return types. For sugar, arguments are
;; a vector of types, rather than the more correct but noisier cat-t
;; of types

(s/fdef fn-t :args (s/cat :f ::fn-args) :ret ::fn-t)
(defn fn-t [m]
  (->> m
       (map (fn [[args ret]]
              [(cat-t args) ret]))
       (into {})
       (conj ['fn])))

(defn-type-pred fn-t? 'fn)

(s/def ::invokeable (s/or :v var? :k keyword? :t tagged?))
(s/fdef invoke-t :args (s/cat :f ::invokeable :args cat-t?) :ret ::type)
(defn-tagged-type invoke-t 'invoke)
(defn-type-pred invoke-t? 'invoke)

(defn any-t? [t]
  (= #'any? t))

(defn object-t? [t]
  (and (class-t? t) (-> t second (= Object))))

(s/fdef type-value :args (s/cat :t tagged?) :ret any?)
(defn type-value [t]
  (when (and (vector? t) (> (count t) 1))
    (nth t 1)))

(s/fdef type-values :args (s/cat :t tagged?) :ret any?)
(defn type-values [t]
  (vec (rest t)))

(def value-value type-value)

(declare or-t)
(declare regex?)

(def types-hierarchy (atom (make-hierarchy)))

(defn predicate-symbol? [x]
  (and (symbol? x)
       (re-find #"\?$" (name x))))

(defn ns-predicates
  "Return all var predicates in ns"
  [ns]
  (->> ns
       (ns-publics)
       (filter (fn [[sym var]]
                 (predicate-symbol? sym)))
       (vals)))

(defn core-predicates []
  (-> 'clojure.core
      (ns-predicates)
      (set)
      (disj #'contains? #'every? #'satisfies? #'isa? #'some? #'future-done? #'empty? #'extends? #'instance? #'identical? #'distinct? #'any?)))


(declare derive-type)

(defn ensure-type-any
  "Ensure that type t derives from #'any?"
  [t]
  (when (and (not= #'any?)
             (not (contains? (ancestors @types-hierarchy t) #'any?)))
    (derive-type #'any? t)))

(defn derive-type
  "clojure.core/derive, but patched to allow vars as tags and parents.

Note arguments are reversed from clojure.core/derive, to resemble (valid? x y)"
  ([h parent tag]
   (assert (not= tag parent))
   (assert (or (class? tag) (instance? clojure.lang.Named tag) (var? tag) (nil? tag)))
   (assert (or (instance? clojure.lang.Named parent) (var? parent)))
   (let [tp (:parents h)
         td (:descendants h)
         ta (:ancestors h)
         tf (fn [m source sources target targets]
              (reduce (fn [ret k]
                        (assoc ret k
                               (reduce conj (get targets k #{}) (cons target (targets target)))))
                      m (cons source (sources source))))]
     (or
      (when-not (contains? (tp tag) parent)
        (when (contains? (ta tag) parent)
          (throw (Exception. (print-str tag "already has" parent "as ancestor"))))
        (when (contains? (ta parent) tag)
          (throw (Exception. (print-str "Cyclic derivation:" parent "has" tag "as ancestor"))))
        {:parents (assoc (:parents h) tag (conj (get tp tag #{}) parent))
         :ancestors (tf (:ancestors h) tag td parent ta)
         :descendants (tf (:descendants h) parent ta tag td)}))))
  ([parent tag]
   (swap! types-hierarchy derive-type parent tag)
   (ensure-type-any parent)
   (ensure-type-any tag)))

(derive-type #'any? 'or)
(derive-type #'any? 'and)
(derive-type #'any? 'cat)
(derive-type #'any? 'seq-of)
(derive-type #'any? 'alt)
(derive-type #'any? #'regex?)
(derive-type #'regex? 'cat)
(derive-type #'regex? 'alt)
(derive-type #'regex? 'seq-of)
(derive-type #'any? 'coll-of)
(derive-type #'any? #'logic?)
(derive-type #'any? 'value)
(derive-type #'any? 'invoke)

(defn load-type-hierarchy []
  (doseq [p (core-predicates)]
    (derive-type #'any? p)))

(load-type-hierarchy)

(s/fdef class-t :args (s/cat :c (s/or :c class? :l logic? :v value-t?)) :ret ::type)
(defn class-t [x]
  (let [cls (if (value-t? x)
              (value-value x)
              x)]
    ['class cls]))

(def seq-value type-value)

(s/fdef cat-t :args (s/cat :t (s/nilable ::types)) :ret ::type)
(defn cat-t [ts]
  (->> ts
       (map (fn [t]
              (if (accept-t? t)
                (type-value t))
              t))
       (apply vector 'cat)))

(s/fdef cat-types :args (s/cat :x cat-t?) :ret (s/coll-of ::type))
(defn cat-types [x]
  (vec (rest x)))

(s/fdef cat-length :args (s/cat :c cat-t?) :ret nat-int?)
(defn cat-length
  "Given a cat, return its length"
  [t]
  (count (cat-types t)))

(s/fdef alt-t :args (s/cat :t (s/coll-of (s/nilable ::type))) :ret (s/nilable ::type))
(defn alt-t [ps]
  (when (seq ps)
    (apply vector 'alt ps)))

(defn alt-types [x]
  (vec (rest x)))

(s/fdef merge-fns :args (s/cat :fns (s/coll-of ::fn-t)) :ret ::fn-t)
(defn merge-fns [fns]
  (fn-t (apply merge (map second fns))))

(s/fdef fn-args :args (s/cat :f ::fn-t) :ret ::type)
(defn fn-args
  "Return an `or` of all arities this fn will accept"
  [f-t]
  (-> f-t second keys (->> or-t)))

(s/fdef fn-ret :args (s/cat :f ::fn-t) :ret ::type)
(defn fn-ret
  "Return an `or` of all types this fn may return"
  [f-t]
  (-> f-t second vals (->> or-t)))

(defn conformy? [t]
  (not (invalid? t)))

(defn ? [x]
  (alt-t [x nil]))

(defn * [x]
  (seq-of x))

(defn + [x]
  (cat-t [x (* x)]))

(defn nilable [x]
  (or-t [#'nil? x]))

(s/fdef not-value :args (s/cat :t not-t?) :ret ::type)
(def not-value type-value)

(s/fdef or-types :args (s/cat :t or-t?) :ret ::types)
(def or-types type-value)

(s/fdef join-not-pairs :args (s/cat :ts ::types) :ret ::types)
(defn join-not-pairs
  "If two types in ts are (not x) and x, replace them with any?"
  [ts]
  (let [ts (set ts)
        {nots true
         _ false} (group-by not-t? ts)]
    (if (seq nots)
      (reduce (fn [ts nott]
                (if-let [s (contains? ts (not-value nott))]
                  (-> ts
                      (disj ts (not-value nott))
                      (disj ts nott)
                      (conj #'any?))
                  ts)) (set ts) nots)
      ts)))

(s/fdef class-value :args (s/cat :t class-t?) :ret (s/or :c class? :t ::type))
(def class-value type-value)

(s/fdef simplify :args (s/cat :t ::type) :ret ::type)
(defn simplify
  "Given a type, convert to it's most precise version"
  [t]
  (let [ts (parents types-hierarchy t)]
    (or (->> ts
             (filter value-t?)
             first)
        (->> ts
             (filter class-t?)
             first)
        (->> ts
             (filter (fn [s]
                       (and (or-t? s)
                            (every? class-t? (or-types s)))))
             first)
        t)))

(s/fdef maybe-value :args (s/cat :m maybe-t?) :ret ::type)
(def maybe-value type-value)

(s/fdef or-consolidate :args (s/cat :ts ::types) :ret ::types)
(defn or-consolidate [ts]
  (let [or-ts (->> ts
                   (filter or-t?)
                   (mapcat or-types))
        maybe-ts (->> ts
                      (filter maybe-t?)
                      (map maybe-value))
        ts (->> ts
                (remove or-t?)
                (remove maybe-t?))
        ts (map simplify ts)
        ts (concat ts or-ts maybe-ts)
        ts (join-not-pairs ts)
        ts (map (fn [t]
                  (if (object-t? t)
                    #'any?
                    t)) ts)
        ;; ts (if (some any-t? ts)
        ;;      (take 1 (filterv any-t? ts))
        ;;      ts)
        ts (set ts)]
    ts))

(s/fdef or-t :args (s/cat :ts ::types) :ret ::type)
(defn or-t [ts]
  (let [ts (or-consolidate ts)]
    (cond
      (>= (count ts) 2) ['or (set ts)]
      (= 1 (count ts)) (first ts)
      :else nil)))

(s/fdef and-classes-compatible? :args (s/cat :ts ::types) :ret boolean?)
(defn and-classes-compatible?
  "True if the `and-t` `class`es are compatible (doesn't contain concrete classes that aren't ancestors)"
  [ts]
  (let [compatible? (fn [a b]
                      {:pre [(class? a) (class? b)]}
                      (and ;; (not (= Object a))
                       (or (isa? a b)
                           (isa? b a)
                           (j/castable? a b)
                           (and (j/interface? a) (j/subclassable? b))
                           (and (j/interface? b) (j/subclassable? a)))))
        ts-classes (->> ts
                        (map simplify)
                        (filter class-t?))]
    (loop [[t-classes & tr-classes] ts-classes]
      (if t-classes
        (if (every? (fn [trs]
                      (some (fn [t]
                              (some (fn [tr]
                                      (compatible? t tr)) trs)) t-classes)) tr-classes)
          (recur tr-classes)
          false)
        true))))

(defn and-nots-compatible?
  "True if ts does not contains ?x and (not-t ?x)"
  [ts]
  {:post [(do (when-not %
                (println "and-nots:" ts "=>" %)) true)]}
  (let [nots (filter not-t? ts)
        not-preds (set (map second nots))]
    (not (some (fn [p]
                 (some (fn [np]
                         (= np p)) not-preds)) ts))))

(defn and-values-compatible?
  "true if `and` ts does not contain two non-equal values"
  [ts]
  {:post [(do (when-not %
                (println "and-value-compatible?" ts "=>" %)) true)]}
  (let [{values true non-values false} (group-by value-t? ts)]
    (if (seq values)
      (apply = (map second values))
      true)))

(defn and-types [a]
  (nth a 1))

(s/fdef and-consolidate :args (s/cat :ts ::types) :ret ::types)
(defn and-consolidate
  "Given the types for an `and`, simplify and consolidate types, returning a seq of types"
  [ts]
  (let [ts-orig ts
        ts (distinct ts)
        ts (map simplify ts)
        {values true not-values false} (group-by value-t? ts)
        ts (if (seq values)
             values
             not-values)
        {ands true not-ands false} (group-by and-t? ts)
        ts (concat (seq not-ands) (distinct (mapcat (fn [a] (and-types a)) ands)))
        {fns true not-fns false} (group-by fn-t? ts)
        ts (if (> (count fns) 1)
             (conj not-fns (merge-fns fns))
             ts)
        ts (distinct ts)
        {anys true not-anys false} (group-by any-t? ts)
        ts (if (seq not-anys)
             not-anys
             (take 1 anys))
        {ors true not-ors false} (group-by or-t? ts)
        ;; ts (if (and (seq ors) (and-or-compatible? ts))
        ;;      ts
        ;;      [(invalid {:message (format "and: or specs incompatible: %s" ts)})])
        ts (if (and-classes-compatible? ts)
             ts
             [(invalid {:message (format "and classes incompatible: %s" ts)})])
        ts (if (and-nots-compatible? ts)
             ts
             [(invalid {:message (format "and nots are incompatible: %s" ts)})])
        ts (if (and-values-compatible? ts)
             ts
             [(invalid {:message (format "and values are incompatible: %s" ts)})])]
    ts))

(s/fdef and-t :args (s/cat :ts ::types) :ret ::type)
(defn and-t [ts]
  (let [{maybe-ts true
         and-ts false} (->> ts
                            (and-consolidate)
                            (group-by maybe-t?))
        and-ts (set and-ts)]
    (cond
      (> (count (filter regex? and-ts)) 1) (invalid {:message (format "can't `and` multiple regexes, got %s" (map print-str ts))})
      (and (seq maybe-ts) (>= (count and-ts) 2)) (or-t (conj (mapv maybe-value maybe-ts) ['and and-ts]))
      (and (seq maybe-ts) (= (count and-ts) 1)) (or-t (conj (mapv maybe-value maybe-ts) (first and-ts)))
      (and (seq maybe-ts) (= 0 (count and-ts))) (-> maybe-ts first maybe-value)
      (>= (count and-ts) 2) ['and and-ts]
      (= 1 (count and-ts)) (first and-ts)
      :else nil)))

(defn and-rest [a]
  (and (rest (and-types a))))

(s/fdef and-conj :args (s/cat :a and-t? :x ::type) :ret ::type)
(defn and-conj
  [s x]
  (and-t (conj (and-types s) x)))

(defmulti regex? #'type-tag)
(defmethod regex? :default [_]
  false)

(defmethod regex? 'cat [x]
  true)

(defmethod regex? 'seq-of [x]
  true)

(defmethod regex? 'alt [x]
  true)

(derive-type #'number? #'integer?)
(derive-type #'number? #'double?)
(derive-type #'integer? #'int?)
(derive-type #'int? #'even?)
(derive-type #'seqable? 'seq-of)
(derive-type #'seqable? 'coll-of)
(derive-type 'coll-of 'vector-of)

(instrument-ns)
