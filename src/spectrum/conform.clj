(ns spectrum.conform
  (:refer-clojure :exclude [vector-of * +])
  (:require [clojure.core :as c]
            [clojure.math.combinatorics :as combo]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.java :as j]
            [spectrum.util :refer [instrument-ns validate!]])
  (:import [clojure.lang IPersistentMap IPersistentSet Sequential]))

;; based on https://eli.thegreenplace.net/2018/unification/
;; https://github.com/clojure/core.unify
;; http://mullr.github.io/micrologic/literate.html


;;; Types are one of:
;;; a var predicate, such as #'int?, representing a value that satisfies that predicate
;;; logic variable: a symbol starting with ?, such as '?a
;;; a vector where the first item is a symbol, and the rest is arbitrary type data. e.g. ['seq-of '?x]

(def ignore? (partial = '_))

(defn logic? [x]
  (or (and (symbol? x) (= \? (-> x name first)))
      (ignore? x)))

(s/def ::type-atom (s/or :lvar logic? :v var? :s symbol?))

(defn tagged? [t]
  (and (vector? t)
       (-> t first symbol?)
       (not (logic? (first t)))))

(s/def ::type (s/or :ta ::type-atom :tagged-type tagged?))
(s/def ::types (s/coll-of ::type))

(declare unify)

(defn type-tag [t]
  (when (and (vector? t) (symbol? (first t)))
    (nth t 0)))

(defn tagged-type? [name x]
  (and (vector? x)
       (= name (first x))))

(defmacro def-type-pred [name tag]
  `(defn ~name [x#]
     (tagged-type? ~tag x#)))

(defmacro defn-tagged-type
  "defn ~name as a fn that constructs a vector tagged type"
  [name tag]
  `(defn ~name [& args#]
     (apply conj [~tag] args#)))

(def-type-pred class-t? 'class)

(defn-tagged-type accept-t 'accept)
(def-type-pred accept-t? 'accept)
(defn-tagged-type invalid 'invalid)
(def-type-pred invalid? 'invalid)

(defn-tagged-type value-t 'value)
(def-type-pred value-t? 'value)

(defn-tagged-type throw-t 'throw)
(defn-tagged-type recur-t 'recur)

(defn-tagged-type protocol-t 'protocol)

(def-type-pred and-t? 'and)
(def-type-pred or-t? 'or)
(def-type-pred not-t? 'not)

(defn-tagged-type not-t 'not)

(def-type-pred cat-t? 'cat)
(def-type-pred alt-t? 'alt)

(defn-tagged-type seq-of 'seq-of)
(def-type-pred seq-t? 'seq-of)

(defn-tagged-type maybe-t 'maybe)
(def-type-pred maybe-t? 'maybe)

(s/fdef map-entry :args (s/cat :x ::type :y ::type) :ret ::type)
(defn-tagged-type map-entry 'map-entry)
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

(s/def ::fn-args (s/map-of :fn/args :fn/ret))
(s/def ::fn-tag #{'fn})
(s/def ::fn-t (s/tuple ::fn-tag ::fn-args))

(s/fdef fn-t :args (s/cat :f ::fn-args) :ret ::fn-t)
(defn-tagged-type fn-t 'fn)
(def-type-pred fn-t? 'fn)

(defn any-t? [t]
  (= #'any? t))

(defn object-t? [t]
  (and (class-t? t) (-> t second (= Object))))

(defn type-value [t]
  (when (and (vector? t) (> (count t) 1))
    (nth t 1)))

(def value-value type-value)

(declare or-t)
(declare regex?)

(s/fdef get-lvars :ret (s/nilable (s/coll-of symbol? :kind set?)))
(defn get-lvars
  "Return a set of logic vars in expression"
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

(defn composite? [x]
  (cond
    (logic? x) false
    (coll? x) true))

(defn occurs?
  "Does v occur anywhere inside typ"
  [v typ subst]
  {:pre [(logic? v)]}
  (cond
    (= v typ) true
    (and (logic? typ) (get subst typ)) (recur v (get subst typ) subst)
    (composite? typ) (some (fn [e] (occurs? v e subst)) (seq typ))
    :else false))

(def types-hierarchy (atom (make-hierarchy)))

(defn unify-term-value [x]
  (cond
    (logic? x) #'logic?
    (tagged? x) (type-tag x)
    (var? x) (if (parents @types-hierarchy x)
               x
               #'any?)
    (nil? x) #'any?
    :else (class x)))

(defn unify-terms-dispatch [u v subst]
  ;; {:post [(do (println "unify terms dispatch" u v "=>" %) true)]}
  [(unify-term-value u) (unify-term-value v)])

(defmulti unify-terms "" #'unify-terms-dispatch :hierarchy types-hierarchy :default [#'any? #'any?])

(s/def ::subst (s/map-of logic? any?))
(s/def ::substs (s/nilable (s/coll-of ::subst :kind sequential?)))

(s/fdef unify-variable-1 :args (s/cat :l logic? :t any? :s ::subst) :ret ::substs)
(defn unify-variable-1 [l t subst]
  {:pre [(map? subst)]}
  (cond
    (get subst l) (unify (get subst l) t [subst])
    (and (logic? t) (get subst t)) (unify l (get subst t) [subst])
    (occurs? l t subst) nil
    :else (do
            (assert (map? subst))
            (if (not (ignore? l))
              [(assoc subst l t)]
              [subst]))))

(s/fdef unify-variable :args (s/cat :v logic? :t any? :s ::substs) :ret ::substs)
(defn unify-variable [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-variable-1 x y s)))
       (filterv identity)))

(s/fdef unify-terms-default :args (s/cat :x any? :y any? :subst ::substs) :ret ::substs)
(defn unify-terms-default [x y substs]
  ;; {:post [(do (println "unify terms default" x y "=>" %) true)]}
  (or
   (when (logic? y)
     (unify-variable y x substs))
   (when (logic? x)
     (unify-variable x y substs))
   (when (any-t? x)
     substs)
   (when (isa? @types-hierarchy y x)
     substs)
   (when (tagged? y)
     (when-let [ancestors (ancestors @types-hierarchy (type-tag y))]
       (->> ancestors
            (some (fn [a]
                    (unify x a substs))))))
   (when-let [ancestors (ancestors @types-hierarchy y)]
       (->> ancestors
            (some (fn [a]
                    (unify x a substs)))))

   nil))

(defmethod unify-terms [#'any? #'any?] [x y subst]
  (unify-terms-default x y subst))

(defmethod unify-terms [#'logic? #'any?] [x y subst]
  (unify-variable x y subst))

(defmethod unify-terms [#'any? #'logic?] [x y subst]
  (unify-variable y x subst))

(defmethod unify-terms [#'logic? #'logic?] [x y subst]
  (unify-variable y x subst))

(defmethod unify-terms [Sequential Object] [x y subst]
  (when (and (seqable? y) (seq y))
    (->> subst
         (unify (first x) (first y))
         (unify (rest x) (rest y)))))

(defmethod unify-terms [IPersistentSet Object] [x y subst]
  (when (and (seqable? y) (seq y))
    (->> subst
         (unify (first x) (first y))
         (unify (rest x) (rest y)))))

(defmethod unify-terms [IPersistentMap IPersistentMap] [x y subst]
  (let [[x-k x-v] (->> x (sort-by (fn [[k v]] (logic? k))) first)]
    ;; (println "unify map" x-k x-v (contains? y x-k) (logic? x-k))
    (cond
      (and (= {} x) (= {} y)) subst
      (contains? y x-k) (->> subst
                             (unify x-v (get y x-k))
                             (unify (dissoc x x-k) (dissoc y x-k)))
      (map? y) (->> (keys y)
                    (map (fn [y-k]
                           (when-let [subst (->> subst
                                                 (unify x-k y-k)
                                                 (unify (get x x-k) (get y y-k)))]
                             [x-k y-k subst])))
                    (filter identity)
                    (first)
                    ((fn [[x-k y-k subst]]
                       (->> subst
                            (unify (dissoc x x-k) (dissoc y y-k)))))))))

(s/fdef unify :args (s/cat :x any? :y any? :substs (s/? ::substs)) :ret ::substs)
(defn unify
  "Unifies term x and y with initial subst.

    Returns a seq of subst maps, (map of name->term) that unify x and y, or nil if
    they can't be unified."
  ([x y]
   (unify x y [{}]))
  ([x y substs]
   ;; {:post [(do (println "unify" x y substs "=>" %) true)]}
   (cond
     (nil? substs) nil
     (= x y) substs
     :else (->> (unify-terms x y substs) seq doall))))

(defmulti accept-nil?
  "True if this (regex) type may accept no input"
  #'type-tag
  :default nil)

(defmethod accept-nil? nil [_]
  false)

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

(defn load-type-hierarchy []
  (doseq [p (core-predicates)]
    (derive-type #'any? p)))

(load-type-hierarchy)

(defn valid? [x y]
  (boolean (seq (unify x y))))

(s/fdef match :args (s/cat :v var? :args (s/coll-of ::type) :ret ::type))
(defn match
  "Pattern match. Given the var to a function with polymorphic behavior, enhance the function's spec."
  [f args ret])

(defn apply-t
  "Given a type, apply with args. Return the return type. Uses pattern matches if available. If no patterns availabe, use the spec"
  [t args])

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
       (c/apply vector 'cat)))

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
    (c/apply vector 'alt ps)))

(defn alt-types [x]
  (vec (rest x)))

(s/def :fn/args ::type)
(s/def :fn/ret ::type)

(s/fdef fn-methods-unifying :args (s/cat :f ::fn-t :args ::type) :ret (s/nilable ::fn-t))
(defn fn-method-unifying
  "Given invoke args, return an updated fn-t containing only the methods that unify, or nil"
  [f-t invoke-args]
  (->> f-t
       (second)
       (filter (fn [[method-args method-ret]]
              (valid? method-args invoke-args)))
       ((fn [ms]
          (when (seq ms)
            (->> ms
                 (apply concat)
                 (apply hash-map)
                 (fn-t)))))))

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

(s/fdef class-value :args (s/cat :t class-t?) :ret (c/or :c class? :t ::type))
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
                         (valid? np p)) not-preds)) ts))))

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
  (c/and (rest (and-types a))))

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

(defmulti disentangle* #'type-tag)
(defmethod disentangle* :default [t]
  [t])

(defn disentangle
  "Given a type containing possible choices, such as `alt` or `or`,
  resolve the choices and return a seq of all possible concrete specs
  that don't contain ambiguity.

(disentangle (cat [(c/? ?t1) ?t2])
=>
([cat ?t1 ?t2] [cat ?t2])"
  [x]
  (or (disentangle* x)
      [x]))

(defmethod disentangle* 'alt [t]
  (let [xs (alt-types t)]
    (->> xs
         (mapcat disentangle)
         (vec))))

(defmethod disentangle* 'or [t]
  (let [xs (or-types t)]
    (->> xs
         (mapcat disentangle)
         (vec))))

(defmethod disentangle* 'cat [t]
  (let [xs (cat-types t)]
    (->> xs
         (mapv disentangle)
         ((fn [xs]
            xs))
         (apply combo/cartesian-product)
         ((fn [xs]
            xs))
         (map (fn [xs]
                (cat-t (filterv identity xs)))))))

(defn fix-length-dispatch [t n]
  (type-tag t))

(defmulti fix-length* #'fix-length-dispatch)

(defmethod fix-length* :default [t n]
  [t])

(s/fdef fix-length :args (s/cat :t ::type :n int?) :ret (s/coll-of ::type))
(defn fix-length
  "Given a type containing variable length regexes, such as ? or *, return a seq of all possible concrete specs of length *up to* `n`. Should be performed after disentangle.

(fix-length (* int?) 2)
=>
[(cat) (cat int?) (cat int? int?)]"
  [t n]
  (fix-length* t n))

(defmethod fix-length* 'seq-of [t n]
  (let [x (seq-value t)]
    (->>
     (repeat n x)
     (reductions conj [])
     (map (fn [x]
            (with-meta (cat-t x) {:splice true}))))))

(defmethod fix-length* 'cat [t n]
  (let [xs (cat-types t)]
    (if (nat-int? n)
      (if-let [x (first xs)]
        (let [fixed-x (->> (fix-length x n)
                           (mapv (fn [x]
                                   (if (cat-t? x)
                                     (cat-types x)
                                     [x]))))
              fixed-xr (->> (fix-length (cat-t (rest xs)) n)
                            (mapv (fn [x]
                                    (if (cat-t? x)
                                      (cat-types x)
                                      x)))
                            (#(or (seq %) [[]])))]
          (->> fixed-x
               (mapcat (fn [fx]
                         (->> fixed-xr
                              (map (fn [xr]
                                     (cat-t (concat fx xr)))))))))
        [(cat-t [])])
      [])))

(defn all-possible-values
  "Given a regex, disentangle and fix length, returning all concrete specs up to length n"
  [t n]
  {:pre [(validate! ::type t)
         (nat-int? n)]}
  (->> t
       (disentangle)
       (mapcat (fn [t]
                 (fix-length t n)))
       (filter (fn [t]
                 (if (cat-t? t)
                   (<= (count (cat-types t)) n)
                   true)))
       (distinct)
       (set)))

(defn all-possible-values-length-n
  "all-possible-values with length == n, but return a single cat, `or`ing together each element"
  [t n]
  (if (conformy? t)
    (->> (all-possible-values t n)
         (filter (fn [t]
                   (= n (cat-length t))))
         (map cat-types)
         ((fn [ts]
            (if (seq ts)
              (cat-t (apply mapv (fn [& es]
                                   (or-t es)) ts))
              (do
                (println "all possible length n" t n)
                (assert false)
                (invalid {:message (format "no possible value of length %s: %s %s" n (print-str t) n)}))))))
    t))

(defn dx-dispatch [x y substs]
  (type-tag x))

(defmulti dx
  #'dx-dispatch)

(defmethod dx 'cat [cat-x y substs]
  (let [[x & xr :as xs] (cat-types cat-x)]
    (if (regex? x)
      (dx x y substs)
      (let [subst (unify x y substs)]
        {:state (when (seq xr)
                  (cat-t xr)) :substs substs}))))

(defmethod dx 'seq-of [seq-x y subst]
  (let [x (seq-value seq-x)]
    (when-let [subst (unify x y subst)]
      {:state seq-x :substs subst})))

(defmethod dx 'alt [alt-x y subst]
  (when-let [subst (unify alt-x y subst)]
    {:state nil :substs subst}))

(defmethod unify-terms ['cat 'cat] [cat-x cat-y substs]
  ;; {:post [(do (println "unify cat cat" cat-x cat-y "=>" %) true)]}
  (let [[x & xr :as xs] (cat-types cat-x)
        [y & yr :as ys] (cat-types cat-y)]
    (->>
     (apply concat
            [(when (and (accept-nil? cat-x) (accept-nil? cat-y))
               substs)
             (if (and (regex? x) y)
               (let [{:keys [state substs]} (dx x y substs)
                     new-y (when (seq yr)
                             (cat-t yr))]
                 (if state
                   (unify (cat-t (concat [state] xr)) (cat-t yr) substs)
                   (unify (cat-t xr) (cat-t yr) substs)))
               (when-let [substs (seq (unify x y substs))]
                 (unify (cat-t xr) (cat-t yr) substs)))
             (when (accept-nil? x)
               (unify (cat-t xr) cat-y substs))
             (when (accept-nil? y)
               (unify cat-x (cat-t yr) substs))])
     (filter identity)
     (distinct)
     (seq))))

(defmethod unify-terms ['seq-of 'cat] [seq-of cat substs]
  (let [x (seq-value seq-of)
        [y & ys] (cat-types cat)]
    (->>
     (apply concat [(->> substs
                         (unify x y)
                         (unify seq-of (cat-t ys)))
                    (when (accept-nil? cat)
                      substs)])
     (filter identity))))

(defmethod unify-terms ['seq-of 'seq-of] [a b subst]
  (let [x (seq-value a)
        y (seq-value b)]
    (unify x y subst)))

(defmethod unify-terms ['coll-of 'coll-of] [a b subst]
  (let [x (type-value a)
        y (type-value b)]
    (unify x y subst)))

(defmethod unify-terms ['or #'any?] [or-x y substs]
  (->> (or-types or-x)
       (mapcat (fn [x]
                 (unify x y substs)))
       (filter identity)
       (distinct)))

(prefer-method unify-terms ['or #'any?] [#'any? #'logic?])

(defmethod unify-terms ['or 'or] [or-x or-y substs]
  (->> or-y
       (or-types)
       (seq)
       (combo/permutations)
       (mapcat (fn [ys]
                 (reduce (fn [substs y]
                           (unify or-x y substs)) substs ys)))
       (filter identity)
       (distinct)))

(defmethod unify-terms ['alt #'any?] [alt-x y substs]
  (->> alt-x
       (alt-types)
       (mapcat (fn [x]
                 (if (nil? x)
                   substs
                   (unify x y substs))))
       (filter identity)
       (distinct)))

(prefer-method unify-terms ['alt #'any?] [#'any? #'logic?])

(defmethod unify-terms ['alt 'alt] [alt-x alt-y substs]
  (->> alt-y
       (alt-types)
       (seq)
       (combo/permutations)
       (mapcat (fn [ys]
                 (reduce (fn [substs y]
                           (unify alt-x y substs)) substs ys)))
       (filter identity)
       (distinct)))

(defmethod accept-nil? 'alt [t]
  (some nil? (alt-types t)))

(defmethod accept-nil? 'seq-of [t]
  true)

(defmethod accept-nil? 'cat [t]
  (every? accept-nil? (cat-types t)))

(defn resolve-type-dispatch [t subst]
  (type-tag t))

(defmulti resolve-type* #'resolve-type-dispatch)

(defmethod resolve-type* :default [t subst]
  nil)

(s/fdef resolve-type :args (s/cat :t (s/nilable ::type) :s map?) :ret (s/nilable ::type))
(defn resolve-type [t subst]
  (let [t* (get subst t t)]
    (cond
      (and (logic? t*) (not= t t*)) (resolve-type t* subst)
      :else (or (resolve-type* t* subst) t*))))

(defmethod resolve-type* 'cat [t subst]
  (cat-t (map #(resolve-type % subst) (cat-types t))))

(defmethod resolve-type* 'fn [t subst]
  (->> (nth t 1)
       (map (fn [[args ret]]
              [(resolve-type args subst) (resolve-type ret subst)]))
       (into {})
       (fn-t)))

(defmethod resolve-type* 'or [t subst]
  (->> t
       (or-types)
       (map #(resolve-type % subst))
       (or-t)
       ((fn [or-t]
          (if (every? fn-t? (or-types or-t))
            (merge-fns (or-types or-t))
            or-t)))))

(defmethod resolve-type* 'and [t subst]
  (->> t
       (and-types)
       (map #(resolve-type % subst))
       (and-t)))

(defmethod resolve-type* 'class [t subst]
  (class-t (resolve-type (class-value t) subst)))

(defmethod resolve-type* 'maybe [t subst]
  (maybe-t (resolve-type (maybe-value t) subst)))

(defmethod resolve-type* 'value [t subst]
  (value-t (resolve-type (type-value t) subst)))

(defmethod unify-terms [#'number? #'integer?] [x y subst]
  subst)

(s/fdef unify-terms-value-pred :args (s/cat :v any? :p var?))
(defn unify-term-value-pred
  "Define unify-terms such that [value `val`] and var `pred` unify, bidirectionally"
  [val pred]
  (defmethod unify-terms ['value pred] [val-x pred-y subst]
    (let [v (type-value val-x)]
      (unify v val subst)))
  (defmethod unify-terms [pred 'value] [pred-x val-y subst]
    (let [v (type-value val-y)]
      (unify val v subst))))

(derive-type #'number? #'integer?)
(derive-type #'number? #'double?)
(derive-type #'integer? #'int?)
(derive-type #'int? #'even?)
(derive-type #'seqable? 'seq-of)
(derive-type #'seqable? 'coll-of)
(derive-type 'coll-of 'vector-of)


(unify-term-value-pred nil #'nil?)
(unify-term-value-pred true #'true?)
(unify-term-value-pred false #'false?)
(unify-term-value-pred 0 #'zero?)

(instrument-ns)
