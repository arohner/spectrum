(ns spectrum.conform2
  (:refer-clojure :exclude [vector-of cat * +])
  (:require [clojure.core :as c]
            [clojure.math.combinatorics :as combo]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.java :as j]
            [spectrum.unify :as u]
            [spectrum.util :refer [instrument-ns validate!]]))

(defn logic? [x]
  (c/and (symbol? x)
         (= \? (-> x name first))))

(s/def ::type-atom (s/or :lvar logic? :v var? :s symbol? ;; :n nil?
                         ))

(defn tagged? [t]
  (and (vector? t)
       (-> t first symbol?)))

(defn type-tag [t]
  (when (and (vector? t) (symbol? (first t)))
    (nth t 0)))

(defn tagged-type? [name x]
  (and (vector? x)
       (= name (first x))))

(defmacro def-type-pred [name tag]
  `(defn ~name [x#]
     (tagged-type? ~tag x#)))

(def-type-pred value-t? 'value)
(def-type-pred class-t? 'class)
(def-type-pred and-t? 'and)

(def-type-pred cat-t? 'cat)

(defn type-value [t]
  (when (and (vector? t) (> (count t) 1))
    (nth t 1)))

(def value-value type-value)

(s/def ::type (s/or :ta ::type-atom :tagged-type tagged?))
(s/def ::types (s/coll-of ::type))

(declare or-t)
(declare regex?)

(defn unify-strict
  "unify, but rightside lvars can't match the whole pattern"
  [a b]
  (let [a-lvars (u/get-lvars a)
        b-lvars (u/get-lvars b)
        subst (u/unify a b)]
    (when (every? (fn [[k v]]
                    (not= v a)) subst)
      subst)))

(def conform-patterns (atom {}))

(defn form-node-count [form]
  (let [node-count (atom 0)]
    (walk/postwalk (fn [f]
                     (swap! node-count inc))
                   form)
    @node-count))

(defn def-pattern [state pat f]
  (let [lvars (u/get-lvars pat)
        replace-map (->> lvars
                         (map (fn [l] [l (u/freshen-lvar l)]))
                         (into {}))
        fresh-form (u/rename replace-map pat)]
    (swap! state assoc (with-meta fresh-form {:replace replace-map}) f)))

(defn pattern-invoke [name state [arg & args]]
  (->> state
       (map (fn [[pat f]]
              (when-let [subst (unify-strict pat arg)]
                (let [replace-map (-> pat meta :replace)
                      unfresh-map (set/map-invert replace-map)
                      subst* (->> subst
                                  (map (fn [[k v]]
                                         [(get unfresh-map k k) (u/rename unfresh-map v)]))
                                  (into {}))]
                  [pat subst* f]))))
       (filter identity)
       (map (fn [[pat subst f]]
              (apply f subst args)))
       (first)))

(defmacro def-pattern-multi
  "Defines a multi-method-like function, that takes a type
  pattern, and a fn that is called when the pattern matches. f takes a
  substitution map, and any extra arguments passed in"
  [def-name invoke-name & args]
  `(do
     (let [state# (atom {})]
       (defn ~def-name [pat# f#]
         (def-pattern state# pat# f#))
       (defn ~invoke-name [& args#]
         (pattern-invoke (quote ~invoke-name) @state# args#)))))

(def-pattern-multi def-conform-strategy find-conform-strategy)

(defmulti accept-nil?
  "True if this type may accept no input"
  #'type-tag
  :default nil)

(defmethod accept-nil? nil [_]
  false)

(def types-hierarchy (atom {}))

(defn def-valid
  "define (valid? x y) => true"
  [x y]
  (swap! types-hierarchy update-in [y] (fnil conj #{}) x))

(defn valid* [x y]
  (c/or (= x #'any?)
        (boolean (unify-strict x y))
        false))

(defn get-ancestors* [t]
  (->> @types-hierarchy
       (mapcat (fn [[y x]]
                 (when-let [subst (u/unify y t)]
                   (u/rename subst x))))
       (filter identity)))

(defn get-ancestors [t]
  (->> (get-ancestors* t)
       (mapcat (fn [t]
                 (concat [t] (get-ancestors t))))
       (distinct)))

(defn valid-ancestor [x y]
  (c/or (valid* x y)
        (->> (get-ancestors y)
             (some #(valid* x %)))))

(defn valid?
  [x y]
  (let [result (valid-ancestor x y)]
    (if result
      result
      (if-let [result (find-conform-strategy [x y])]
        result
        false))))

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

(s/fdef seq-of :args (s/cat :t ::type) :ret ::type)
(defn seq-of [x]
  ['seq-of x])

(def seq-value type-value)

(s/fdef cat :args (s/cat :t (s/nilable ::types)) :ret ::type)
(defn cat-t [ps]
  (c/apply vector 'cat ps))

(s/fdef cat-types :args (s/cat :x cat-t?) :ret (s/coll-of ::type))
(defn cat-types [x]
  (vec (rest x)))


(s/fdef cat-length :args (s/cat :c cat-t?) :ret nat-int?)
(defn cat-length
  "Given a cat, return its length"
  [t]
  (count (cat-types t)))

(s/fdef alt :args (s/cat :t (s/coll-of (s/nilable ::type))) :ret (s/nilable ::type))
(defn alt [ps]
  (when (seq ps)
    (c/apply vector 'alt ps)))

(defn alt-types [x]
  (vec (rest x)))

(s/def :fn/args ::type)
(s/def :fn/ret ::type)

(s/def ::fn-args (s/map-of :fn/args :fn/ret))
(s/def ::fn-tag #{'fn})
(s/def ::fn-t (s/tuple ::fn-tag ::fn-args))

(s/fdef fn-t :args (s/cat :f ::fn-args) :ret ::fn-t)
(defn fn-t [args]
  ['fn args])

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

(def-type-pred fn-t? 'fn)

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

(defn accept [x]
  ['accept x])

(defn accept? [x]
  (= 'accept (first x)))

(defn invalid [args]
  ['invalid args])

(def-type-pred invalid? 'invalid)

(defn conformy? [t]
  (not (invalid? t)))

(defn ? [x]
  (alt [x nil]))

(defn * [x]
  (seq-of x))

(defn + [x]
  (cat-t [x (* x)]))

(defn coll-of [x]
  ['coll-of x])

(defn map-entry [x y]
  ['map-entry x y])

(defn vector-of [x]
  ['vector-of x])

(defn nilable [x]
  (or-t [#'nil? x]))

(defn throw-t [x]
  ['throw x])

(defn recur-t [x]
  ['recur x])

(defn value-t [x]
  ['value x])

(defn protocol-t [p]
  ['protocol p])

(def-type-pred or-t? 'or)
(def-type-pred not-t? 'not)

(defn not-t [t]
  ['not t])

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

(s/fdef class-value :args (s/cat :t class-t?) :ret ::type)
(def class-value type-value)

(defn object-t? [t]
  (and (class-t? t) (-> t second (= Object))))

(s/fdef simplify :args (s/cat :t ::type) :ret ::type)
(defn simplify
  "Given a type, convert to it's most precise version"
  [t]
  (let [ts (get-ancestors t)]
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

(defn any-t? [t]
  (= #'any? t))

(defn maybe-t
  "Indicates that the value might be ?x, in addition to any other
  types via other equations. All `maybe`s are `or`'d together
  during unification"
  [?x]
  ['maybe ?x])

(def-type-pred maybe-t? 'maybe)

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

(s/def :keys/req (s/coll-of ::type))
(s/def :keys/req-un (s/coll-of ::type))
(s/def :keys/opt (s/coll-of ::type))
(s/def :keys/opt-un (s/coll-of ::type))
(s/fdef keys-t :args (s/cat :k (s/keys :opt-un [:keys/req :keys/req-un :keys/opt :keys/opt-un])))
(defn keys-t [x]
  ['keys x])

(defn dx-dispatch [x y]
  (type-tag x))

(defmulti dx #'dx-dispatch)

(defmethod dx :default [_ _]
  nil)

(def-conform-strategy '[[or ?xs] ?y] (fn [{:syms [?xs ?y]}]
                                       (some (fn [?x]
                                               (valid? ?x ?y)) ?xs)))

;; (def-conform-strategy ['or (u/contains #{'?x})] '?x true)

(def-conform-strategy '[?x [and ?y]] (fn [{:syms [?x ?y]}]
                                       (valid? ?x (u/contains ?y))))

;; (def-conform-strategy ['or '?x] ['and '?y] (fn [?x ?y]
;;                                              (->>
;;                                               ?y
;;                                               (some (fn [y]
;;                                                       (valid? []))))

;;                                              ))

;; (def-conform-strategy ['and '?x] ['or '?y] (fn [x y]
;;                                              ;; (if (and? y)
;;                                              ;; (valid? x (u/contains (and-types y)))
;;                                              ;; false)
;;                                              ))

(def-conform-strategy '[[and ?x] [and ?y]] (fn [{:syms [?x ?y]}]
                                             (->> ?x
                                                  (some (fn [x]
                                                          (valid? x (and-t ?y)))))))

(def-conform-strategy '[[or ?x] [or ?y]] (fn [{:syms [?x ?y]}]
                                           (->> ?y
                                                (every? (fn [y]
                                                          (valid? (or-t ?x) y))))))

(defmulti regex? #'type-tag)
(defmethod regex? :default [_]
  false)

(defmethod regex? 'cat [x]
  true)

(defmethod regex? 'seq-of [x]
  true)

(defmethod regex? 'alt [x]
  true)

(defmethod dx 'cat [cat y]
  (let [[x & xs] (cat-types cat)]
    (cond
      (regex? x) (let [ret (dx x y)]

                    (cond
                      (accept? ret) (cat-t xs)
                      ret (cat-t (concat [ret] xs))
                      (accept-nil? x) (dx (cat-t xs) y)))
      (valid? x y) (cat-t xs))))

(defmethod dx 'seq-of [s y]
  (let [x (seq-value s)]
    (when (valid? x y)
      (seq-of x))))

(defmethod dx 'alt [a y]
  (let [xs (alt-types a)]
    (->> xs
         (map (fn [x]
                (when (valid? x y)
                  (accept x))))
         (filter identity)
         first)))

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

(def-conform-strategy '[[cat & ?xs] [cat & ?ys]] (fn [{:syms [?xs ?ys]}]
                                                   (let [?x (first ?xs)
                                                         ?y (first ?ys)
                                                         ret (dx (cat-t ?xs) ?y)]
                                                     (cond
                                                       (and ret (accept-nil? ret) (accept-nil? (cat-t (rest ?ys)))) true
                                                       ret (valid? ret (cat-t (rest ?ys)))))))

(def-conform-strategy '[[seq-of ?x] [cat & ?ys]] (fn [{:syms [?x ?ys]}]
                                                   (let [?y (first ?ys)]
                                                     (c/or
                                                      (c/and (valid? ?x ?y)
                                                             (valid? (seq-of ?x) (cat-t (rest ?ys))))
                                                      (nil? ?ys)))))

(def-conform-strategy '[[cat ?x & ?xs] [seq-of ?y]] (fn [{:syms [?x ?xs ?y]}]
                                                      (c/and (valid? ?x ?y)
                                                             (valid? (cat-t ?xs) (seq-of ?y)))))

(def-conform-strategy '[[alt ?x & ?xs] ?y] (fn [{:syms [?x ?xs ?y] :as subst}]
                                             (c/or (valid? ?x ?y)
                                                   (valid? (alt ?xs) ?y)
                                                   (when (and (nil? ?x) (nil? ?xs))
                                                     true))))

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

;; (defn unify-var [x y subst]
;;   (cond
;;     (= x #'any?) subst
;;     (= y #'any?) subst))

;; (extend-protocol u/IUnifyTerms
;;   clojure.lang.Var
;;   (unify-terms* [x y subst]
;;     (unify-var x y subst)))

(s/fdef resolve-type :args (s/cat :t ::type :s map?) :ret (s/nilable ::type))
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
       (or-t)))

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

(def-valid #'number? #'integer?)
(def-valid #'number? #'double?)
(def-valid #'integer? #'int?)
(def-valid #'int? #'even?)
(def-valid #'seqable? (seq-of '?x))
(def-valid #'seqable? (coll-of '?x))

(def-valid (coll-of '?x) (vector-of '?x))

(instrument-ns)
