(ns spectrum.types
  (:refer-clojure :exclude [vector-of * + parents ancestors descendants gen-class])
  (:require [clojure.core :as core]
            [clojure.math.combinatorics :as combo]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.test.check.generators :as gen]
            [clojure.walk :as walk]
            [spectrum.java :as j]
            [spectrum.util :refer [instrument-ns defn-memo]])
  (:import clojure.lang.Var))

(declare alt-t)
(declare and-t)
(declare and-t?)
(declare cat-t)
(declare class-cast)
(declare class-t)
(declare coll-of)
(declare coll-of?)
(declare derive-type)
(declare fn-t?)
(declare or-t)
(declare or-t?)
(declare regex?)
(declare seq-of)
(declare sort-ts)
(declare sort-ts)
(declare spec-t)
(declare value-t)
(declare vector-of)

(defn logic? [x]
  (and (symbol? x) (= \? (-> x name (.charAt 0)))))

(s/fdef logic-name :args (s/cat :l logic?) :ret string?)
(defn logic-name [x]
  (as-> x %
    (name %)
    (re-find #"^\?(\p{Lower}+[-+±]?)" %)
    (second %)))

(defn logic-number
  [x]
  (some->> x
           name
           (re-find #"^\?\p{Lower}+[-+±]?(\d+)$")
           second
           (Integer/parseInt)))

(defn bound-t? [t subst]
  (and (logic? t) (boolean (find subst t))))

(def type-counter (atom -1))

(defn reset-type-counter! []
  (reset! type-counter -1))

(s/fdef new-logic :args (s/cat :prefix (s/? (s/or :str string? :l logic?))) :ret logic?)
(defn new-logic
  ([]
   (new-logic "t"))
  ([t]
   (let [next (swap! type-counter inc)]
     (symbol (str "?" (if (logic? t) (logic-name t) t) next)))))

(defn mapwalk
  "walk an arbitrary structure similar to clojure.walk/postwalk, but non-destructive. Returns nil"
  [f form]
  (cond
    (seqable? form) (dorun (map (partial mapwalk f) form))
    :else (f form))
  nil)

(s/fdef get-lvars :ret (s/nilable (s/coll-of symbol? :kind set?)))
(defn get-lvars
  "Return a set of logic variables in expression"
  [expr]
  (let [lvars (atom #{})]
    (mapwalk (fn [f] (when (logic? f)
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
        replace-map (->> lvars (map (fn [l] [l (if (logic-number l)
                                                 l
                                                 (new-logic (logic-name l)))])) (into {}))]
    (println "freshen" replace-map)
    (rename replace-map form)))

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

;; things that appear to be predicates by their name, but aren't
;; because of signature. We can automate this once we infer better

(def not-core-predicates #{#'bound?
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

(defonce value-pred-whitelist (atom #{}))

(s/fdef add-value-pred-whitelist! :args (s/cat :v var?))
(defn add-value-pred-whitelist!
  "Declare var predicate v as safe for calling to unify with values. v
  should be a predicate, pure (free of side-effects) and fast"
  [v]
  (swap! value-pred-whitelist conj v))

(doseq [v (core-predicates)]
  (add-value-pred-whitelist! v))

(s/def ::var-t (s/with-gen var? #(gen/elements (core-predicates))))


(s/def ::logic (s/with-gen logic? (fn []
                                    (gen/fmap (fn [n]
                                                (symbol (str "?t" n))) gen/nat))))
(s/def ::type-atom (s/or :l ::logic :v ::var-t :n nil?))

(s/def ::fresh-logic (s/and logic? logic-number))
(s/def ::fresh-type-atom (s/or :s ::fresh-logic :v var?))

(defn tagged? [t]
  (and (vector? t)
       (pos? (count t))
       (-> t (nth 0) var?)))

(s/def ::cat (s/cat :c #{'cat} :ts (s/* ::type)))

(defn fresh-tagged? [t]
  (and (vector? t)
       (pos? (count t))
       (-> t (nth 0) var?)
       (not (logic? (nth t 0)))
       (every? logic-number (get-lvars t))))

(def ^:dynamic *current-depth* 0)
(def max-depth 1)

(declare gen-tagged)

(def gen-atom (s/gen (s/spec ::type-atom)))

(defn gen-type [depth]
  (if (pos? depth)
    (gen/one-of [(s/gen (s/spec ::type-atom))
                 (gen-tagged (dec depth))])
    (s/gen (s/spec ::type-atom))))

(defn gen-alt [depth]
  (gen/fmap (fn [ts]
              (alt-t ts)) (gen/vector (gen-type (dec depth)) 2 3)))

(defn gen-nilable [depth]
  (gen/fmap (fn [t]
              (alt-t [t nil])) (gen-type (dec depth))))

(defn gen-spec [depth]
  (gen/fmap (fn [t]
              (spec-t t)) (gen-type depth)))

(declare gen-cat)
(declare gen-seq-of)

(defn gen-re [depth]
  (gen/one-of [(gen-alt depth)
               (gen-nilable depth)
               (gen-cat depth)
               (gen-seq-of depth)
               (gen-spec depth)
               (gen-type depth)]))

(defn gen-cat [depth]
  (let [depth (dec depth)
        gen (if (pos? depth)
              (gen-re depth)
              (gen-type depth))]
    (gen/fmap (fn [ts]
                (cat-t ts)) (gen/vector gen 0 3))))

(defn gen-or [depth]
  (gen/such-that or-t?
                 (gen/fmap (fn [ts]
                             (or-t ts)) (gen/vector (gen-type (dec depth)) 2 4))))

(defn gen-and [depth]
  (gen/such-that and-t?
                 (gen/fmap (fn [ts]
                             (and-t ts)) (gen/vector (gen-type (dec depth)) 2 4))))

(defn gen-seq-of [depth]
  (gen/fmap (fn [t]
              (seq-of t)) (gen-type (dec depth))))

(defn gen-coll-of [depth]
  (gen/fmap (fn [t]
              (coll-of t)) gen-atom))

(defn gen-vector-of [depth]
  (gen/fmap (fn [t]
              (vector-of t)) gen-atom))

(def gen-class (gen/elements [clojure.lang.Reversible
                              clojure.lang.ReaderConditional
                              clojure.lang.Associative
                              clojure.lang.IPersistentVector
                              clojure.lang.Keyword
                              java.util.UUID
                              clojure.lang.Sorted
                              java.lang.Number
                              clojure.lang.IFn
                              clojure.lang.IPersistentSet
                              clojure.lang.IPersistentCollection
                              clojure.lang.TaggedLiteral
                              clojure.lang.Delay
                              clojure.lang.IPersistentList
                              java.net.URI
                              java.lang.Class
                              clojure.lang.Volatile
                              clojure.lang.ISeq
                              java.util.Date
                              clojure.lang.Counted
                              clojure.lang.Var
                              clojure.lang.Indexed
                              clojure.lang.Ratio
                              java.math.BigDecimal
                              java.lang.Double
                              clojure.lang.Sequential
                              java.lang.Object
                              clojure.lang.IPersistentMap
                              clojure.lang.IChunkedSeq
                              java.lang.Character
                              java.lang.Boolean
                              java.lang.String
                              clojure.lang.Fn
                              clojure.lang.Symbol
                              java.util.concurrent.Future
                              java.util.Map$Entry]))

(def gen-class-t (gen/fmap (fn [t]
                             (class-t t)) gen-class))

(def gen-value (gen/fmap (fn [t]
                           (value-t t)) gen/any))

(defn gen-tagged [depth]
  (gen/one-of [(gen-cat depth)
               (gen-or depth)
               (gen-and depth)
               (gen-seq-of depth)
               (gen-coll-of depth)
               gen-class-t
               gen-value]))

(s/def ::tagged (s/with-gen
                  (s/and vector?
                         (fn [x]
                           (when (> (count x) 0)
                             (let [t (nth x 0)]
                               (and (var? t)
                                    (predicate-symbol? (.sym ^Var t)))))))
                  #(gen-tagged 2)))

(s/def ::type (s/or :ta ::type-atom
                    :tt ::tagged))

(s/def ::fresh-type (s/or :ta ::fresh-type-atom :tagged-type fresh-tagged?))

(defn type? [x]
  (s/valid? ::type x))

(s/def ::types (s/coll-of ::type))

(defn type-tag [t]
  (when (and (vector? t) (pos? (count t)))
    (nth t 0)))

(defn tagged-type?
  "True if t is a tagged type with symbol `name`"
  [name t]
  (and (vector? t)
       (pos? (count t))
       (= name (nth t 0))))

(defmacro defn-type-pred [name]
  (assert (predicate-symbol? name))
  `(do
     (declare ~name)
     ;; (add-)
     (defn ~name [x#]
       (tagged-type? (var ~name) x#))
     (add-value-pred-whitelist! (var ~name))))

(s/fdef defn-tagged-type :args (s/cat :name symbol? :pred symbol?))
(defmacro defn-tagged-type
  "defn ~name as a fn that constructs a vector tagged type"
  [constructor pred]
  `(do
     (defn-type-pred ~pred)
     (defn ~constructor [& args#]
       (apply conj [(var ~pred)] args#))))

(defn-type-pred class-t?)

(defn-tagged-type accept-t accept-t?)
(defn-tagged-type invalid invalid?)

(defn conformy? [t]
  (not (invalid? t)))

(defn-tagged-type value-t value-t?)
(s/fdef value-t :args (s/cat :x any?) :ret value-t?)

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
    [#'class-t? cls]))

(defn-tagged-type throw-t throw-t?)
(defn-tagged-type recur-t recur-t?)

(defn-tagged-type protocol-t protocol-t?)

(defn-type-pred and-t?)
(defn or-t? [x]
  (and (tagged? x)
       (= #'or-t? (nth x 0))
       (vector? (nth x 1))))

(defn-type-pred or-t?)

(defn-tagged-type not-t not-t?)

(defn-type-pred cat-t?)
(defn-type-pred alt-t?)
(defn-type-pred seq-of?)

(defn seq-of [x]
  [#'seq-of? (if (seq-of? x)
               (type-value x)
               x)])

;; same idea as seq-of, but it's a thing that is seqable, rather than an actual seq
(defn-tagged-type seqable-of seqable-of?)

(defn-tagged-type maybe-t maybe-t?)

(s/fdef map-entry :args (s/cat :x ::type :y ::type) :ret ::type)
(defn-tagged-type map-entry map-entry-t?)

(defn-tagged-type map-of map-of?)

(defn-tagged-type coll-of coll-of?)

(defn-tagged-type spec-t spec-t?)

(s/fdef vector-of :args (s/cat :x ::type) :ret ::type)
(defn-tagged-type vector-of vector-of?)

(defn-tagged-type set-of set-of?)

(s/def :keys/key-class (s/map-of keyword? ::type))

(s/def :keys/req :keys/key-class)
(s/def :keys/req-un :keys/key-class)
(s/def :keys/opt :keys/key-class)
(s/def :keys/opt-un :keys/key-class)
(s/fdef keys-t :args (s/cat :k (s/keys :opt-un [:keys/req :keys/req-un :keys/opt :keys/opt-un])))
(defn-tagged-type keys-t keys-t?)

(s/def ::fn-args-in (s/or :ta (s/coll-of ::type :kind vector?) :cat cat-t?))
(s/def :fn/args cat-t?)
(s/def :fn/ret ::type)
(s/def ::fn-args (s/map-of :fn/args :fn/ret))
(s/def ::fn-tag #{#'fn-t?})
(s/def ::fn-t (s/tuple ::fn-tag ::fn-args))

;; fns are maps of arguments to return types. For sugar, arguments may
;; be a vector of types, rather than the more correct but noisier
;; cat-t of types

(s/fdef maybe-cat :args (s/cat :o (s/or :ts ::types :c cat-t? :t ::type)) :ret ::type)
(defn maybe-cat [args]
  (cond
    (cat-t? args) args
    (s/valid? ::types args) (cat-t args)
    :else args))

(defn-type-pred fn-t?)

(s/fdef fn-t :args (s/cat :f (s/map-of ::fn-args-in :fn/ret)) :ret ::fn-t)
(defn fn-t [m]
  (->> m
       (map (fn [[args ret]]
              [(maybe-cat args) ret]))
       (into {})
       (conj [#'fn-t?])))

(defn-tagged-type invoke-t invoke-t?)

(s/fdef invoke-t :args (s/cat :f ::type :args (s/or :c cat-t? :i invoke-t?)) :ret ::type)
(defn any-t? [t]
  (= #'any? t))

(defn object-t? [t]
  (and (class-t? t) (-> t second (= Object))))

(def types-hierarchy (atom (make-hierarchy)))

(s/fdef derive-type :args (s/cat :h (s/? any?) :parent ::type :type ::type))
(defn derive-type
  "clojure.core/derive, but patched to allow types.

Note arguments are reversed from clojure.core/derive, to resemble (valid? x y)"
  ([h parent type]
   (assert (not= type parent) (format "derive-type: can't derive %s -> %s" parent type))
   (assert h)
   (when (var? parent)
     (assert (predicate-symbol? (.sym parent)) "derive must be named predicate"))
   (when (var? type?)
     (assert (predicate-symbol? (.sym type)) "derive must be named predicate"))
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

(s/fdef parents :args (s/cat :t (s/or :t ::type)) :ret (s/nilable (s/coll-of (s/or :t ::type))))
(defn parents
  "Same as clojure.core/parents, but for types"
  [t]
  (->> [(core/parents @types-hierarchy t)
        (when (tagged? t)
          (->> (type-tag t)
               (core/parents @types-hierarchy)))
        (when (class-t? t)
          (map class-t (core/parents (type-value t))))]
       (apply concat)
       (filter identity)
       (distinct)
       seq))

(defn descendants [t]
  (-> @types-hierarchy
      :descendants
      (get t)))

(def seq-value type-value)

(s/fdef cat-t :args (s/cat :t ::types) :ret ::type)
(defn cat-t [ts]
  (->> ts
       ;; (mapv (fn [t]
       ;;         (if (accept-t? t)
       ;;           (type-value t))
       ;;         t))
      (apply vector #'cat-t?)))

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
    (apply vector #'alt-t? ps)))

(defn alt-types [x]
  (vec (rest x)))

(s/fdef merge-fns :args (s/cat :fns (s/coll-of ::fn-t)) :ret (s/nilable ::fn-t))
(defn merge-fns [fns]
  (when (seq fns)
    (->> fns
         (map second)
         (apply merge)
         (fn-t))))

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

(s/fdef class-value :args (s/cat :t class-t?) :ret (s/or :c class? :t ::type))
(def class-value type-value)

(def equiv-types
  (atom {}))

(s/fdef get-equiv-types :args (s/cat :hm (s/? (s/map-of any? any?)) :t any?) :ret (s/nilable (s/coll-of any?)))
(defn get-equiv-types
  ([t]
   (get-equiv-types @equiv-types t))
  ([equiv-types t]
   (or (get equiv-types t)
       (when (tagged? t)
         (get equiv-types (type-tag t))))))

(defn instance-or-t?
  [t]
  (and (or-t? t)
       (every? (fn [t]
                 (or (class-t? t)
                     (class-cast t))) (type-value t))))

(defn-memo canonicalize*
  [equiv-types t]
  (let [ts (conj (get-equiv-types equiv-types t) t)]
    (->> (concat (filter value-t? ts)
                 (filter var? ts)
                 (filter (fn [t*] (and (tagged? t*)
                                       (not (class-t? t*))
                                       (not (instance-or-t? t*)))) ts)
                 [t])
         (first))))

(s/fdef canonicalize :args (s/cat :t any?) :ret any?)
(defn canonicalize
  "Given a type, convert to it's most precise version"
  [t]
  (canonicalize* @equiv-types t))

(s/fdef set-equiv-types! :args (s/cat :x ::type :x ::type))
(defn set-equiv-types!
  "Define types x and y as being equivalent"
  [x y]
  (swap! equiv-types update x (fnil conj #{}) y)
  (swap! equiv-types update y (fnil conj #{}) x)
  nil)

(s/fdef ancestors :args (s/cat :t ::type) :ret (s/coll-of ::type))
(defn ancestors [t]
  (->> t
       (parents)
       (mapcat (fn [p]
                 (concat [p] (parents p))))
       (mapcat (fn [t]
                 (concat [t] (get-equiv-types t))))
       (filter identity)
       (set)
       (#(disj % t))))

(defn class-cast
  "cast to class-t if the type can be cast _without losing precision_, else nil"
  [t]
  (let [ts (conj (get-equiv-types t) t)]
    (->> (concat (filter class-t? ts)
                 (filter instance-or-t? ts))
         (first))))

(defn class-ancestors
  "ancestors that are also class-t, or convertible to class-t"
  [t]
  (let [ts (conj (ancestors t) (class-cast t))]
    (->>
     ts
     (mapcat get-equiv-types)
     (concat ts)
     (distinct)
     (filter (fn [t]
               (or (class-t? t)
                   (instance-or-t? t)))))))

(s/fdef maybe-value :args (s/cat :m maybe-t?) :ret ::type)
(def maybe-value type-value)

(s/fdef join-not-pairs :args (s/cat :ts (s/coll-of any?)) :ret (s/coll-of any?))
(defn join-not-pairs
  "If two types in ts are (not x) and x, replace them with any?"
  [ts]
  (let [ts (set ts)
        {nots true
         _ false} (group-by not-t? ts)
        nots (map (fn [nt]
                    (not-t (canonicalize (not-value nt)))) nots)]
    (if (seq nots)
      (reduce (fn [ts nott]
                (if-let [s (contains? ts (not-value nott))]
                  (-> ts
                      (disj ts (not-value nott))
                      (disj ts nott)
                      (conj #'any?))
                  ts)) (set ts) nots)
      ts)))

(s/fdef or-consolidate :args (s/cat :ts (s/coll-of any?)) :ret (s/coll-of any?))
(defn or-consolidate [ts]
  (let [or-ts (->> ts
                   (filter or-t?)
                   (mapcat type-value))
        maybe-ts (->> ts
                      (filter maybe-t?)
                      (map maybe-value))
        fn-ts (->> ts
                   (filter fn-t?))
        ts (->> ts (remove fn-t?))
        ts (if (seq fn-ts)
             (conj ts (merge-fns fn-ts))
             ts)
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
             (take 1 (filterv any-t? ts))
             ts)
        ts (distinct ts)]
    (vec (sort-ts ts))))

(s/fdef or-t :args (s/cat :ts (s/coll-of (s/nilable ::type))) :ret (s/nilable ::type))
(defn or-t [ts]
  {:post [(if (and (vector? %) (= #'or-t? (nth % 0)))
            (or-t? %)
            true)]}
  (let [ts (if (> (count ts) 1)
             (or-consolidate ts)
             ts)]
    (cond
      (>= (count ts) 2) [#'or-t? ts]
      (= 1 (count ts)) (nth ts 0)
      :else nil)))

(s/fdef and-classes-compatible? :args (s/cat :ts ::types) :ret boolean?)
(defn and-classes-compatible?
  "True if the `and-t` `class`es are compatible (doesn't contain concrete classes that aren't ancestors)"
  [ts]
  (let [compatible? (fn [a b]
                      {:pre [(do
                               (when-not (class? a)
                                 (println "and-compatible?" a (class a) ts))
                               true)
                             (class? a) (class? b)]}
                      (and ;; (not (= Object a))
                       (or (isa? a b)
                           (isa? b a)
                           (j/castable? a b)
                           (and (j/interface? a) (j/subclassable? b))
                           (and (j/interface? b) (j/subclassable? a)))))
        ts-classes (->> ts
                        (map canonicalize)
                        (filter class-t?)
                        (map type-value)
                        (filter class?))]
    (loop [[t-class & tr-classes] ts-classes]
      (if t-class
        (if (every? (fn [tr]
                   (compatible? t-class tr)) tr-classes)
          (recur tr-classes)
          false)
        true))))

(defn and-nots-compatible?
  "True if ts does not contains ?x and (not-t ?x)"
  [ts]
  {:post [(do (when-not %
                (println "and-nots:" ts "=>" %)) true)]}
  (let [nots (filter not-t? ts)
        not-preds (distinct (map second nots))]
    (not (some (fn [p]
                 (some (fn [np]
                         (= np p)) not-preds)) ts))))

(defn and-values-compatible?
  "true if `and` ts does not contain two non-equal values"
  [ts]
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
        ts (map canonicalize ts)
        ts (distinct ts)
        {values true not-values false} (group-by value-t? ts)
        ;; ts (if (seq values)
        ;;      values
        ;;      not-values)
        regexes (filter (fn [t] (and (tagged? t) (regex? t))) ts)
        ts (if (> (count regexes) 1)
             [(invalid {:message (print-str "can't `and` multiple regexes, got" regexes)})]
             ts)
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
        ts (if (and-classes-compatible? ts)
             ts
             [(invalid {:message (format "and classes incompatible: %s" ts)})])
        ts (if (and-nots-compatible? ts)
             ts
             [(invalid {:message (format "and nots are incompatible: %s" ts)})])
        ts (if (and-values-compatible? ts)
             ts
             [(invalid {:message (format "and values are incompatible: %s" ts)})])
        ts (sort-ts ts)]
    ts))

(s/fdef and-t :args (s/cat :ts ::types) :ret ::type)
(defn and-t [ts]
  (let [and-ts (->> ts and-consolidate vec)]
    (cond
      (>= (count and-ts) 2) [#'and-t? and-ts]
      (= 1 (count and-ts)) (first and-ts)
      :else nil)))

(defn and-rest [a]
  (and (rest (and-types a))))

(defn depth-dispatch [t]
  (cond
    (var? t) :var
    (logic? t) :logic
    (tagged? t) (type-tag t)
    :else :any))

(defmulti depth
  "If the type is composite, return the depth of type nodes in
  tree. Return 0 for vars. Returns 1 for logic vars that resolve to
  vars with one substition. Returns ##Inf for recursive types"
  #'depth-dispatch)

(defmethod depth :var [t]
  0)

(defmethod depth :any [t]
  0)

(defmethod depth :logic [t]
  1)

(defn depth-tagged-1 [t]
  {:post [(nat-int? %)]}
  (->> t
       type-value
       depth
       inc))

(defn depth-tagged-n [t]
  {:post [(nat-int? %)]}
  (or
   (some->> t
            type-values
            (map (fn [t*]
                   (depth t*)))
            (seq)
            (apply max)
            (inc))
   1))

(defn depth-tagged-default [t]
  (if (coll? (type-value t))
    (depth-tagged-n t)
    (depth-tagged-1 t)))

(defmethod depth :default [t]
  (cond
    (tagged? t) (depth-tagged-default t)
    :else (assert false (format "don't know how to depth %s" (or (type-tag t) t)))))

(defmethod depth 'cat [t]
  (or
   (some->> t
            rest
            (map (fn [t*]
                   (depth t*)))
            (seq)
            (apply max)
            (inc))
   1))

(defn regex? [x]
  (and (tagged? x)
       (or (contains? #{#'cat-t? #'seq-of? #'alt-t?} (type-tag x))
           (and (= #'value-t? (type-tag x)) (coll? (type-value x))))))

(defn sort-ts-value [x]
  (cond
    (logic? x) #'logic?
    (tagged? x) (if (parents x)
                    (type-tag x)
                    #'any?)
    (var? x) #'var?
    :else #'any?))

(defn sort-ts-compare-dispatch [x y]
  [(sort-ts-value x) (sort-ts-value y)])

(defmulti sort-ts-compare #'sort-ts-compare-dispatch :hierarchy types-hierarchy :default [#'any? #'any?])

(defmethod sort-ts-compare [#'any? #'any?] [x y]
  (compare (depth x) (depth y)))

(defn var-name [v]
  (str (.ns v) "/" (.sym v)))

(defmethod sort-ts-compare [#'var? #'var?] [x y]
  (compare (var-name x) (var-name y)))

(defmethod sort-ts-compare [#'logic? #'logic?] [x y]
  (let [ret (compare (depth x) (depth y))]
    (if (= 0 ret)
      (compare (str x) (str y))
      ret)))

(def sort-comparator (reify
                       java.util.Comparator
                       (compare [this x y]
                         (sort-ts-compare x y))))
(defn sort-ts [ts]
  (sort sort-comparator ts))

(defn derived?
  "True when (derive-type parent type) already exists"
  [parent type]
  (contains? (set (ancestors type)) parent))

(defn isa-t?
  "True if b isa a. Does not check logic variables"
  [a b]
  (cond
    (= a b) true
    (and (tagged? a) (tagged? b)) (contains? (conj (ancestors b) (type-tag b)) (type-tag a))
    (contains? (ancestors b) a) true
    :else false))

(defn instance-t?
  "true if v is an instance of type t"
  [t v]
  (assert (var? t))
  (assert (predicate-symbol? (.sym t)))
  (let [v* (when (tagged? v)
             (nth v 0))]
    (or (t v)
        (when v*
          (isa-t? t v*)))))

(defn ensure-derive-type
  [parent type]
  (when-not (derived? parent type)
    (derive-type parent type)))

(defn load-type-hierarchy []
  (doseq [p (disj (core-predicates) #'any?)]
    (ensure-derive-type #'any? p)))

(load-type-hierarchy)

(instrument-ns)

(derive-type #'any? #'class-t?)
(derive-type #'any? #'or-t?)
(derive-type #'any? #'and-t?)
(derive-type #'any? #'regex?)
(derive-type #'regex? #'cat-t?)
(derive-type #'regex? #'alt-t?)
(derive-type #'regex? #'seq-of?)
(derive-type #'any? #'coll-of?)
(derive-type #'any? #'logic?)
(derive-type #'any? #'value-t?)
(derive-type #'any? #'invoke-t?)
(derive-type #'any? #'spec-t?)

(derive-type #'ifn? #'fn?)
(derive-type #'fn? #'fn-t?)



nil
