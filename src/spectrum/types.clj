(ns spectrum.types
  (:refer-clojure :exclude [vector-of * + parents ancestors])
  (:require [clojure.core :as core]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.java :as j]
            [spectrum.util :refer [instrument-ns defn-memo]]))

(def ignore? (partial = '_))

(defn logic? [x]
  (or (and (symbol? x) (= \? (-> x name first)))
      (ignore? x)))

(s/fdef logic-name :args (s/cat :l logic?) :ret string?)
(defn logic-name [x]
  (as-> x %
    (name %)
    (re-find #"^\?(.*)$" %)
    (second %)))

(def type-counter (atom -1))

(defn new-logic
  ([]
   (new-logic "t"))
  ([prefix]
   (let [next (swap! type-counter inc)]
     (symbol (str "?" prefix next)))))

(s/fdef get-lvars :ret (s/nilable (s/coll-of symbol? :kind set?)))
(defn get-lvars
  "Return a set of logic variables in expression"
  [expr]
  (let [lvars (atom #{})]
    (walk/postwalk (fn [f]
                     (when (logic? f)
                       (swap! lvars conj f)))
                   expr)
    @lvars))

(defn rename
  "Given a map of lvars to lvars, walk form and replace all instances
  of keys values"
  [m form]
  (walk/postwalk (fn [f]
                   (if (logic? f)
                     (if-let [v (get m f)]
                       v
                       f)
                     f))
                 form))

(defn freshen
  "Walk form, replacing all logic variables with unique versions"
  [form]
  (let [lvars (get-lvars form)
        replace-map (->> lvars (map (fn [l] [l (new-logic (logic-name l))])) (into {}))]
    (println "freshen" replace-map)
    (rename replace-map form)))

(s/def ::type-atom (s/or :lvar logic? :v var?))

(defn tagged? [t]
  (and (vector? t)
       (-> t first symbol?)
       (not (logic? (first t)))))

(s/def ::type (s/or :ta ::type-atom :tagged-type tagged? :n nil?))

(defn type? [x]
  (s/valid? ::type x))

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

(s/fdef type-value :args (s/cat :t tagged?) :ret any?)
(defn type-value [t]
  (when (and (vector? t) (> (count t) 1))
    (nth t 1)))

(s/fdef type-values :args (s/cat :t tagged?) :ret any?)
(defn type-values [t]
  (vec (rest t)))

(def value-value type-value)

(s/fdef class-t :args (s/cat :c (s/or :c class? :l logic? :v value-t?)) :ret ::type)
(defn class-t [x]
  (let [cls (if (value-t? x)
              (value-value x)
              x)]
    ['class cls]))

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

(defn-tagged-type spec-t 'spec)
(defn-type-pred spec-t? 'spec)

(s/fdef vector-of :args (s/cat :x ::type) :ret ::type)
(defn-tagged-type vector-of 'vector-of)

(s/def :keys/key-class (s/map-of keyword? ::type))

(s/def :keys/req :keys/key-class)
(s/def :keys/req-un :keys/key-class)
(s/def :keys/opt :keys/key-class)
(s/def :keys/opt-un :keys/key-class)
(s/fdef keys-t :args (s/cat :k (s/keys :opt-un [:keys/req :keys/req-un :keys/opt :keys/opt-un])))
(defn-tagged-type keys-t 'keys)

(s/def ::fn-args-in (s/or :ta (s/coll-of ::type :kind vector?) ::t ::type))
(s/def :fn/args ::type)
(s/def :fn/ret ::type)
(s/def ::fn-args (s/map-of :fn/args :fn/ret))
(s/def ::fn-tag #{'fn})
(s/def ::fn-t (s/tuple ::fn-tag ::fn-args))

;; fns are maps of arguments to return types. For sugar, arguments are
;; a vector of types, rather than the more correct but noisier cat-t
;; of types

(s/fdef maybe-cat :args (s/cat :o (s/or :ts ::types :c cat-t? :t ::type)) :ret ::type)
(defn maybe-cat [args]
  (cond
    (cat-t? args) args
    (s/valid? ::types args) (cat-t args)
    :else args))

(s/fdef fn-t :args (s/cat :f (s/map-of ::fn-args-in :fn/ret)) :ret ::fn-t)
(defn fn-t [m]
  (->> m
       (map (fn [[args ret]]
              [(maybe-cat args) ret]))
       (into {})
       (conj ['fn])))

(defn-type-pred fn-t? 'fn)

(defn-tagged-type invoke-t 'invoke)
(defn-type-pred invoke-t? 'invoke)

(s/fdef invoke-t :args (s/cat :f ::type :args (s/or :c cat-t? :i invoke-t?)) :ret ::type)

(defn any-t? [t]
  (= #'any? t))

(defn object-t? [t]
  (and (class-t? t) (-> t second (= Object))))

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

;; things that appear to be named predicates, but aren't. We can automate this once we infer better
(def not-core-predicates #{#'any?
                           #'bound?
                           #'contains?
                           #'distinct?
                           #'empty?
                           #'every?
                           #'even?
                           #'extends?
                           #'future-cancelled?
                           #'future-done?
                           #'identical?
                           #'instance?
                           #'isa?
                           #'neg?
                           #'odd?
                           #'not-any?
                           #'not-every?
                           #'pos?
                           #'realized?
                           #'satisfies?
                           #'some?
                           #'thread-bound?
                           #'zero?})
(defn core-predicates []
  (-> 'clojure.core
      (ns-predicates)
      (set)
      (set/difference not-core-predicates)))

(declare derive-type)

(s/fdef derive-type :args (s/cat :h (s/? any?) :parent (s/or :t ::type :s symbol?) :type (s/or :t ::type :s symbol?)))
(defn derive-type
  "clojure.core/derive, but patched to allow types.

Note arguments are reversed from clojure.core/derive, to resemble (valid? x y)"
  ([h parent type]
   (assert (not= type parent))
   (assert h)
   (let [tp (:parents h)
         td (:descendants h)
         ta (:ancestors h)
         tf (fn [m source sources target targets]
              (reduce (fn [ret k]
                        (assoc ret k
                               (reduce conj (get targets k #{}) (cons target (targets target)))))
                      m (cons source (sources source))))]
     (when-not tp
       (println "derive-type:" parent type "no tp"))
     (assert tp)
     (assert ta)
     (assert td)
     (assert tf)
     (when-not (contains? (tp type) parent)
       (when (contains? (ta type) parent)
         (throw (Exception. (print-str type "already has" parent "as ancestor"))))
       (when (contains? (ta parent) type)
         (throw (Exception. (print-str "Cyclic derivation:" parent "has" type "as ancestor"))))
       {:parents (assoc (:parents h) type (conj (get tp type #{}) parent))
        :ancestors (tf (:ancestors h) type td parent ta)
        :descendants (tf (:descendants h) parent ta type td)})))
  ([parent type]
   ;; (ensure-type-any parent)
   ;; (ensure-type-any type)
   (let [ret (derive-type @types-hierarchy parent type)]
     (when ret
       (reset! types-hierarchy ret)))))

(s/fdef parents :args (s/cat :t ::type) :ret (s/nilable (s/coll-of (s/or :t ::type :s symbol?))))
(defn parents
  "Same as clojure.core/parents, but for types"
  [t]
  (->> [(core/parents @types-hierarchy t)
        (when (tagged? t)
          (core/parents @types-hierarchy (type-tag t)))
        (when (class-t? t)
          (map class-t (core/parents (type-value t))))]
       (apply concat)
       (filter identity)
       (distinct)
       seq))

(s/fdef ancestors :args (s/cat :t ::type) :ret (s/nilable (s/coll-of ::type)))
(defn ancestors [t]
  (->> t
       (parents)
       (mapcat (fn [p]
                 (concat [p] (parents p))))
       (distinct)
       (filter identity)))

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

(derive-type #'ifn? 'fn)

(defn load-type-hierarchy []
  (doseq [p (core-predicates)]
    (derive-type #'any? p)))

(load-type-hierarchy)

(derive-type (class-t clojure.lang.ISeq) 'seq-of)

(def seq-value type-value)

(s/fdef cat-t :args (s/cat :t (s/nilable ::types)) :ret ::type)
(defn cat-t [ts]
  (->> ts
       (map (fn [t]
              (when-not t
                (println "invalid cat-t:" ts))
              (assert t)
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

(s/fdef simplify-arities :args (s/cat :m (s/map-of ::type ::type)) :ret (s/map-of ::type ::type))
(defn simplify-arities
  "Merge fn arities with the same return type and same number of arguments"
  [fn-map]
  (->> fn-map
       (group-by (fn [[args ret]]
                   (assert (cat-t? args))
                   [ret (count args)]))
       (map (fn [[[_  arg-count] arities]]
              (let [args (map first arities)
                    ret (-> arities first val)]
                [(or-t args) ret])))
       (into {})))

(s/fdef merge-fns :args (s/cat :fns (s/coll-of ::fn-t)) :ret (s/nilable ::fn-t))
(defn merge-fns [fns]
  (when (seq fns)
    (->> fns
         (map second)
         (apply merge)
         (simplify-arities)
         (fn-t))))

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

(s/fdef or-types :args (s/cat :t or-t?) :ret any?)
(def or-types type-value)

(s/fdef join-not-pairs :args (s/cat :ts (s/coll-of any?)) :ret (s/coll-of any?))
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

(def equiv-types
  (atom {}))

(s/fdef set-equiv-types! :args (s/cat :x ::type :x ::type))
(defn set-equiv-types!
  "Define types x and y as being equivalent"
  [x y]
  (swap! equiv-types update x (fnil conj #{}) y)
  (swap! equiv-types update y (fnil conj #{}) x)
  nil)

(s/fdef get-equiv-types :args (s/cat :t any?) :ret (s/nilable (s/coll-of any?)))
(defn get-equiv-types
  ""
  [t]
  (or (get @equiv-types t)
      (when (tagged? t)
        (get @equiv-types (type-tag t)))))

(declare class-cast)

(defn instance-or-t?
  [t]
  (and (or-t? t)
       (every? (fn [t]
                 (or (class-t? t)
                     (class-cast t))) (or-types t))))

(s/fdef canonicalize :args (s/cat :t any?) :ret any?)
(defn-memo canonicalize
  "Given a type, convert to it's most precise version"
  [t]
  (let [ts (conj (get-equiv-types t) t)]
    (->> (concat (filter value-t? ts)
                 (filter var? ts)
                 (filter (fn [t*] (and (tagged? t*)
                                       (not (class-t? t*))
                                       (not (instance-or-t? t*)))) ts)
                 [t])
         (first))))

(defn class-cast
  "cast to class-t If the type can be cast without losing precision, else nil"
  [t]
  (let [ts (conj (get-equiv-types t) t)]
    (->> (concat (filter class-t? ts)
                 (filter instance-or-t? ts))
         (first))))

(s/fdef maybe-value :args (s/cat :m maybe-t?) :ret ::type)
(def maybe-value type-value)

(s/fdef or-consolidate :args (s/cat :ts (s/coll-of any?)) :ret (s/coll-of any?))
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
        ts (map canonicalize ts)
        ts (concat ts or-ts maybe-ts)
        ts (join-not-pairs ts)
        ts (map (fn [t]
                  (if (object-t? t)
                    #'any?
                    t)) ts)
        ts (if (some any-t? ts)
             (do
               ;; (when (> (count ts) 1)
               ;;   (println "WARNING: or-t" ts "=>" #'any?))
               (take 1 (filterv any-t? ts)))
             ts)
        ts (set ts)]
    ts))

(s/fdef or-t :args (s/cat :ts (s/coll-of any?)) :ret any?)
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
                        (map canonicalize)
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
        ts (map canonicalize ts)
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

(instrument-ns)
