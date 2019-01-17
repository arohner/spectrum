(ns spectrum.conform
  (:require [clojure.core :as c]
            [clojure.math.combinatorics :as combo]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.data :as data]
            [spectrum.java :as j]
            [spectrum.types :as t]
            [spectrum.util :refer [instrument-ns validate! defn-memo]])
  (:import [clojure.lang IPersistentMap IPersistentSet Sequential]))

;; based on https://eli.thegreenplace.net/2018/unification/
;; https://github.com/clojure/core.unify
;; http://mullr.github.io/micrologic/literate.html

(declare unify)
(declare resolve-type)

;;; Types are one of:
;;; a var predicate, such as #'int?, representing a value that satisfies that predicate
;;; logic variable: a symbol starting with ?, such as '?a
;;; a vector where the first item is a symbol, and the rest is arbitrary type data. e.g. ['seq-of '?x]

(s/fdef get-lvars :ret (s/nilable (s/coll-of symbol? :kind set?)))
(defn get-lvars
  "Return a set of logic variables in expression"
  [expr]
  (let [lvars (atom #{})]
    (walk/postwalk (fn [f]
                     (when (t/logic? f)
                       (swap! lvars conj f)))
                   expr)
    @lvars))

(defn rename
  "Given a map of lvars to lvars, walk form and replace all instances
  of keys values"
  [m form]
  (walk/postwalk (fn [f]
                   (if (t/logic? f)
                     (if-let [v (get m f)]
                       v
                       f)
                     f))
                 form))

(defn composite? [x]
  (cond
    (t/logic? x) false
    (coll? x) true))

(defn occurs?
  "Does v occur anywhere inside typ"
  [v typ subst]
  {:pre [(t/logic? v)]}
  (cond
    (= v typ) true
    (and (t/logic? typ) (get subst typ)) (recur v (get subst typ) subst)
    (composite? typ) (some (fn [e] (occurs? v e subst)) (seq typ))
    :else false))

(defn dx-dispatch [x y substs]
  (t/type-tag x))

(defmulti dx
  #'dx-dispatch
  :default :default)

(declare unify-terms-dispatch)

(defmulti unify-terms "" #'unify-terms-dispatch :hierarchy t/types-hierarchy :default [#'any? #'any?])

(defn-memo unify-terms-methods []
  (-> unify-terms .getMethodTable keys set))

(defn-memo dx-methods []
  (-> dx .getMethodTable keys set))

(defn dx? [t]
  (contains? (dx-methods) (t/type-tag t)))

(defn unify-term-value [x]
  (cond
    (t/logic? x) #'t/logic?
    (dx? x) #'dx?
    (t/tagged? x) (t/type-tag x)
    (var? x) (if (parents @t/types-hierarchy x)
               x
               #'any?)
    (nil? x) nil
    :else (class x)))

(defn unify-terms-method?
  "Is there a *direct* dispatch value for (unify-terms x y)?"
  [x y]
  (contains? (unify-terms-methods) [x y]))

(defn unify-terms-dispatch [x y subst]
  ;; {:post [(do (println "unify terms dispatch" x y "=>" %) true)]}
  (or (when (unify-terms-method? x y)
        [x y])
      [(unify-term-value x) (unify-term-value y)]))

(s/def ::subst (s/map-of t/logic? any?))
(s/def ::substs (s/nilable (s/coll-of ::subst :kind sequential?)))

(s/fdef unify-variable-1 :args (s/cat :l t/logic? :t any? :s ::subst) :ret ::substs)
(defn unify-variable-1 [l t subst]
  {:pre [(map? subst)]}
  (cond
    (get subst l) (unify (get subst l) t [subst])
    (and (t/logic? t) (get subst t)) (unify l (get subst t) [subst])
    (occurs? l t subst) nil
    :else (do
            (assert (map? subst))
            (if (not (t/ignore? l))
              [(assoc subst l t)]
              [subst]))))

(s/fdef unify-variable :args (s/cat :v t/logic? :t any? :s ::substs) :ret ::substs)
(defn unify-variable [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-variable-1 x y s)))
       (filter identity)))

(s/fdef unify-terms-default :args (s/cat :x any? :y any? :subst ::substs) :ret ::substs)
(defn unify-terms-default [x y substs]
  ;; {:pre [(do (println "default unify terms" x y "pre") true)]
  ;;  :post [(do (println "default unify terms" x y "=>" %) true)]}
  (assert substs)
  (or
   (when (t/logic? y)
     (unify-variable y x substs))
   (when (t/logic? x)
     (unify-variable x y substs))
   (when (t/any-t? x)
     substs)
   (when (isa? @t/types-hierarchy y x)
     substs)
   (when (not (instance? Class y))
     (when-let [ancestors (ancestors @t/types-hierarchy y)]
       (->> ancestors
            (some (fn [a]
                    (unify x a substs))))))
   (when (t/tagged? y)
     (when-let [ancestors (ancestors @t/types-hierarchy (t/type-tag y))]
       (->> ancestors
            (some (fn [a]
                    (unify x a substs))))))
   nil))

(defmethod unify-terms [#'any? #'any?] [x y subst]
  (unify-terms-default x y subst))

(defmethod unify-terms [#'t/logic? #'any?] [x y subst]
  (unify-variable x y subst))

(defmethod unify-terms [#'any? #'t/logic?] [x y subst]
  (unify-variable y x subst))

(defmethod unify-terms [#'t/logic? #'t/logic?] [x y subst]
  (unify-variable y x subst))

(defmethod unify-terms [Sequential Object] [x y subst]
  (when (and (seqable? y) (seq y))
    (some->> subst
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defmethod unify-terms [IPersistentSet Object] [x y subst]
  (when (and (seqable? y) (seq y))
    (some->> subst
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defmethod unify-terms [IPersistentMap IPersistentMap] [x y subst]
  (let [[x-k x-v] (->> x (sort-by (fn [[k v]] (t/logic? k))) first)]
    ;; (println "unify map" x-k x-v (contains? y x-k) (t/logic? x-k))
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

(def ^:dynamic *unify-recursion-count* 0)

(defn verify-unify [x y old-substs new-substs]
  (when new-substs
    (let [old-ks-min (->> old-substs (map (comp set keys)) (apply set/intersection))
          old-ks-max (->> old-substs (map (comp set keys)) (apply set/union))
          valid? (every? (fn [s]
                           {:post [(do (when-not %
                                         (println "substs missing keys:" old-ks-min old-ks-max (set (keys s)) "=>" (set/difference old-ks-min (set (keys s))) s)) true)]}
                           (= old-ks-min (set/intersection old-ks-min (set (keys s))))) new-substs)
          ]
      (when (not valid?)
        (println "verify unify:" x y "old:" old-substs "new:" new-substs)
        (assert false))))
  true)

(defn unify-canonical [x y substs]
  ;; {:post [{:post [(do (println "unify canonical" (t/canonicalize x) (t/canonicalize y) "=>" %) true)]}]}
  (let [x* (t/canonicalize x)
        y* (t/canonicalize y)]
    (->> (unify-terms x* y* substs)
         (filter identity)
         distinct
         seq)))

(defn unify-class [x y]
  ;; {:post [(do (println "unify class" (t/class-cast x) (t/class-cast y) "=>" %) true)]}
  (let [x* (t/class-cast x)
        y* (t/class-cast y)]
    (when (and x* y* (->> (unify-terms x* y* [{}])
                          (filter identity)
                          distinct
                          seq))
      [{}])))

(defn cacheable? [x y]
  (and (= #{} (get-lvars x))
       (= #{} (get-lvars y))))

(defn unify* [x y substs]
  (unify-canonical x y substs))

(defn-memo unify-cache [x y]
  (or
   (or
    (unify-canonical x y [{}])
    (unify-class x y))))

(s/fdef unify :args (s/cat :x any? :y any? :substs (s/? ::substs)) :ret ::substs)
(defn unify
  "Unifies term x and y with initial subst.

    Returns a seq of subst maps, (map of name->term) that unify x and y, or nil if
    they can't be unified."
  ([x y]
   (unify x y [{}]))
  ([x y substs]
   {;; :pre [(do (println "unify pre" x y) true)]
    ;; :post [(do (println "unify" x y "=>" (boolean (seq %))) true)]
    }
   (assert substs)
   (cond
     (= x y) substs
     (cacheable? x y) (when (unify-cache x y)
                        substs)
     :else (unify* x y substs))))

(defmulti accept-nil?
  "True if this (regex) type may accept no input"
  #'t/type-tag
  :default nil)

(defmethod accept-nil? nil [_]
  false)

(defn valid? [x y]
  (boolean (seq (unify x y))))

(s/fdef match :args (s/cat :v var? :args (s/coll-of ::t/type) :ret ::t/type))
(defn ann
  "Given the var to a function with polymorphic behavior, enhance the function's spec. `match` is a pattern to unify on. `args` and `ret` are both seqs of equations "
  [v fn-t])

(defmulti disentangle* #'t/type-tag)
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
  (let [xs (t/alt-types t)]
    (->> xs
         (mapcat disentangle)
         (vec))))

(defmethod disentangle* 'or [t]
  (let [xs (t/or-types t)]
    (->> xs
         (mapcat disentangle)
         (vec))))

(defmethod disentangle* 'cat [t]
  (let [xs (t/cat-types t)]
    (->> xs
         (mapv disentangle)
         ((fn [xs]
            xs))
         (apply combo/cartesian-product)
         ((fn [xs]
            xs))
         (map (fn [xs]
                (t/cat-t (filter identity xs)))))))

(defn fix-length-dispatch [t n]
  (t/type-tag t))

(defmulti fix-length* #'fix-length-dispatch)

(defmethod fix-length* :default [t n]
  [t])

(s/fdef fix-length :args (s/cat :t ::t/type :n int?) :ret (s/coll-of ::t/type))
(defn fix-length
  "Given a type containing variable length regexes, such as ? or *, return a seq of all possible concrete specs of length *up to* `n`. Should be performed after disentangle.

(fix-length (* int?) 2)
=>
[(cat) (cat int?) (cat int? int?)]"
  [t n]
  (fix-length* t n))

(defmethod fix-length* 'seq-of [t n]
  (let [x (t/seq-value t)]
    (->>
     (repeat n x)
     (reductions conj [])
     (map (fn [x]
            (with-meta (t/cat-t x) {:splice true}))))))

(defmethod fix-length* 'cat [t n]
  (let [xs (t/cat-types t)]
    (if (nat-int? n)
      (if-let [x (first xs)]
        (let [fixed-x (->> (fix-length x n)
                           (mapv (fn [x]
                                   (if (t/cat-t? x)
                                     (t/cat-types x)
                                     [x]))))
              fixed-xr (->> (fix-length (t/cat-t (rest xs)) n)
                            (mapv (fn [x]
                                    (if (t/cat-t? x)
                                      (t/cat-types x)
                                      x)))
                            (#(or (seq %) [[]])))]
          (->> fixed-x
               (mapcat (fn [fx]
                         (->> fixed-xr
                              (map (fn [xr]
                                     (t/cat-t (concat fx xr)))))))))
        [(t/cat-t [])])
      [])))

(defn all-possible-values
  "Given a regex, disentangle and fix length, returning all concrete specs up to length n"
  [t n]
  {:pre [(validate! ::t/type t)
         (nat-int? n)]}
  (->> t
       (disentangle)
       (mapcat (fn [t]
                 (fix-length t n)))
       (filter (fn [t]
                 (if (t/cat-t? t)
                   (<= (count (t/cat-types t)) n)
                   true)))
       (distinct)
       (set)))

(defn all-possible-values-length-n
  "all-possible-values with length == n, but return a single cat, `or`ing together each element"
  [t n]
  (if (t/conformy? t)
    (->> (all-possible-values t n)
         (filter (fn [t]
                   (= n (t/cat-length t))))
         (map t/cat-types)
         ((fn [ts]
            (if (seq ts)
              (t/cat-t (apply mapv (fn [& es]
                                   (t/or-t es)) ts))
              (do
                (println "all possible length n" t n)
                (assert false)
                (t/invalid {:message (format "no possible value of length %s: %s %s" n (print-str t) n)}))))))
    t))

(defn first-dispatch [t]
  (t/type-tag t))

(defmulti first-t
  "For regexes, returns a seq of possible values of calling `first` on
  the type"
  #'first-dispatch)

(defmethod first-t 'cat [cat-t]
  (let [[x & xr] (t/cat-types cat-t)]
    (if x
      (if (t/regex? x)
        (->>
         (concat (first-t x) (when (accept-nil? x)
                               (first-t (t/cat-t xr))))
         (filter identity)
         ((fn [ts]
            (if (accept-nil? cat-t)
              (conj ts nil)
              ts)))
         (distinct))
        [x])
      [nil])))

(defmethod first-t 'seq-of [t]
  (-> t
      (t/seq-value)
      ((fn [x]
         (if (t/regex? x)
           (first-t x)
           [x nil])))))

(defmethod first-t 'alt [alt-t]
  (->> alt-t
       t/alt-types
       (mapcat (fn [t]
                 (if (t/regex? t)
                   (first-t t)
                   [t])))))

(s/def :dx/state (s/nilable ::t/type))
(s/def ::dx-ret (s/keys :req-un [:dx/state ::substs]))

(s/def ::dx-rets (s/nilable (s/coll-of ::dx-ret)))

(defmethod dx :default [x y substs]
  (when-let [substs (unify x y substs)]
    [{:state nil :substs substs}]))

(defmethod dx 'cat [cat-x y substs]
  (let [[x & xr :as xs] (t/cat-types cat-x)]
    (->> [(when-let [res (seq (dx x y substs))]
            (->> res
                 (map (fn [{:keys [state substs]}]
                        (when substs
                          {:state (cond
                                    state (t/cat-t (concat [state] xr))
                                    (seq xr) (t/cat-t xr)
                                    :else nil)
                           :substs substs})))))
          (when (accept-nil? x)
            (dx (t/cat-t xr) y substs))]
         (apply concat)
         (filter identity))))

(defmethod dx 'seq-of [seq-x y subst]
  (let [x (t/seq-value seq-x)
        subst (unify x y subst)]
    [{:state nil :substs subst}
     {:state seq-x :substs subst}]))

(defmethod dx 'alt [alt-x y substs]
  (->> (t/alt-types alt-x)
       (mapcat (fn [at]
              (dx at y substs)))))

(defmethod unify-terms [#'dx? #'dx?] [tx ty substs]
  (let [xs (first-t tx)
        ys (first-t ty)]
    (->> xs
         (mapcat (fn [x]
                   (->> ys
                        (mapcat (fn [y]
                                  (let [dx-rets (dx tx y substs)
                                        dy-rets (dx ty y substs)]
                                    (->> dx-rets
                                         (mapcat (fn [dx-ret]
                                                   (->> dy-rets
                                                        (mapcat (fn [dy-ret]
                                                                  (let [{dx-x :state substs :substs} dx-ret
                                                                        {dy-y :state} dy-ret]
                                                                    (->>
                                                                     [(when (and substs
                                                                                 dx-x
                                                                                 dy-y
                                                                                 (or (not= tx dx-x)
                                                                                     (not= ty dy-y)))
                                                                        (unify dx-x dy-y substs))
                                                                      (when (and substs
                                                                                 (or (nil? dx-x) (accept-nil? dx-x))
                                                                                 (or (nil? dy-y) (accept-nil? dy-y)))
                                                                        substs)]
                                                                     (apply concat)))))))))))))))
         (concat
          (when (and (accept-nil? tx) (accept-nil? ty))
            substs))
         (distinct))))

(defmethod unify-terms ['seq-of #'any?] [a b subst]
  (let [x (t/seq-value a)]
    (unify x b subst)))

(prefer-method unify-terms ['seq-of #'any?] [#'any? #'t/logic?])

(defmethod unify-terms ['coll-of 'coll-of] [a b subst]
  (let [x (t/type-value a)
        y (t/type-value b)]
    (unify x y subst)))

(defmethod unify-terms ['or #'any?] [or-x y substs]
  (->> (t/or-types or-x)
       (mapcat (fn [x]
                 (unify x y substs)))))

(prefer-method unify-terms ['or #'any?] [#'any? #'t/logic?])

(defmethod unify-terms ['or 'or] [or-x or-y substs]
  (->> or-y
       (t/or-types)
       (seq)
       (combo/permutations)
       (mapcat (fn [ys]
                 (reduce (fn [substs y]
                           (when substs
                             (unify or-x y substs))) substs ys)))))

(defmethod unify-terms ['alt #'any?] [alt-x y substs]
  (->> alt-x
       (t/alt-types)
       (mapcat (fn [x]
                 (if (nil? x)
                   substs
                   (unify x y substs))))))

(defmethod unify-terms ['class 'class] [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(defmethod unify-terms [nil #'any?] [x y subst]
  nil)

(defmethod unify-terms [nil nil] [x y substs]
  substs)

(prefer-method unify-terms ['alt #'any?] [#'any? #'t/logic?])

(defmethod accept-nil? 'alt [t]
  (some nil? (t/alt-types t)))

(defmethod accept-nil? 'seq-of [t]
  true)

(defmethod accept-nil? 'cat [t]
  (every? accept-nil? (t/cat-types t)))

(defn apply-invoke-dispatch [it subst]
  (let [f (t/type-value it)]
    (cond
      (t/tagged? f) (t/type-tag f)
      (keyword? f) :keyword
      (var? f) #'var?)))

(defmulti apply-invoke #'apply-invoke-dispatch)

(s/def ::apply-invoke-ret (s/nilable (s/coll-of (s/tuple ::t/type ::subst))))

(defmethod apply-invoke :default [it subst]
  {:post [(do (println "apply-invoke default:" it "=>" %) true)]}
  nil)

(defn printable-invoke-t [it]
  (if-let [v (-> it (nth 1) meta :var)]
    (assoc it 1 v)
    it))

(defmethod apply-invoke 'fn [it substs]
  (let [[f invoke-args] (t/type-values it)
        substs-old substs]
    (->> (nth f 1)
         (mapcat (fn [[f-args f-ret]]
                   (when-let [substs (seq (unify f-args invoke-args substs))]
                     (->> substs
                          (map (fn [subst]
                                 [(resolve-type f-ret subst) subst]))))))
         (filter identity)
         (distinct))))

(defmethod apply-invoke 'map-of [it subst]
  (assert false "TODO"))

(defmethod apply-invoke 'keys [it subst]
  (assert false "TODO"))

(defmethod apply-invoke :keyword [it subst]
  (assert false "TODO"))

(defn get-var-type [v]
  (or (data/get-ann v)
      ;;(parse/get-spec v)
      (data/get-var-spec v)))

(defmethod apply-invoke #'var? [it subst]
  (let [v (nth it 1)
        _ (assert (var? v))
        t (get-var-type v)
        t (with-meta t {:var v})]
    (assert (t/fn-t? t))
    (apply-invoke (assoc it 1 t) subst)))

(defn thunk
  "Utility/test fn. Given an invoke, return all possible return types"
  [f args]
  (-> (t/invoke-t f (t/maybe-cat args))
      (apply-invoke [{}])
      (->>
       (map first)
       seq)))

(defmethod unify-terms [#'any? 'invoke] [x invoke-y subst]
  ;; {:pre [(do (println "unify any invoke pre" x invoke-y) true)]
  ;;  :post [(do (println "unify any invoke:" x invoke-y subst "=>" %) true)]}
  (->> (apply-invoke invoke-y subst)
       (mapcat (fn [[y subst]]
                 (unify x y [subst])))))

(defmethod unify-terms ['invoke #'any?] [invoke-x y subst]
  (->>
   (apply-invoke invoke-x subst)
   (mapcat (fn [[x* subst]]
             (unify x* y [subst])))))

(prefer-method unify-terms [#'any? 'invoke] [#'t/logic? #'any?])
(prefer-method unify-terms [#'any? 'invoke] ['or #'any?])
(prefer-method unify-terms ['invoke #'any?] [#'any? #'t/logic?])

;; (defmethod unify-terms ['value #'any?] [v y substs]
;;   (unify (t/type-value v) y substs))

;; (defmethod unify-terms [#'any? 'value] [x v substs]
;;   (unify x (t/type-value v) substs))

(defmethod unify-terms ['value 'value] [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(prefer-method unify-terms [#'any? 'value] [#'t/logic? #'any?])
(prefer-method unify-terms ['value #'any?] [#'any? #'t/logic?])

(s/fdef unify-terms-equiv :args (s/cat :x ::t/type :y ::t/type))
(defn unify-terms-equiv
  "Define unify-terms such that x and y unify, bidirectionally"
  [x y]
  (defmethod unify-terms [x y] [x y subst]
    subst)
  (defmethod unify-terms [y x] [y x subst]
    subst)
  (prefer-method unify-terms [#'any? #'t/logic?] [x y])
  (prefer-method unify-terms [#'t/logic? #'any?] [y x]))

(defn derive-all-any
  "We need all tagged types to derive from #'any?, so default dispatching works"
  []
  (->> (unify-terms-methods)
       (apply concat)
       distinct
       (filter symbol?)
       (map (fn [s]
              (t/derive-type #'any? s)))
       (dorun)))

(derive-all-any)
(t/derive-type #'any? #'dx?)
nil

(defn resolve-type-dispatch [t subst]
  (t/type-tag t))

(defmulti resolve-type* #'resolve-type-dispatch)

(defmethod resolve-type* :default [t subst]
  nil)

(s/fdef resolve-type :args (s/cat :t #'any? :s ::subst) :ret #'any?)
(defn resolve-type [t subst]
  (let [t* (get subst t t)]
    (cond
      (and (t/logic? t*) (not= t t*)) (resolve-type t* subst)
      :else (or (resolve-type* t* subst) t*))))

(defmethod resolve-type* 'cat [t subst]
  (t/cat-t (map #(resolve-type % subst) (t/cat-types t))))

(defmethod resolve-type* 'fn [t subst]
  (->> (nth t 1)
       (map (fn [[args ret]]
              [(resolve-type args subst) (resolve-type ret subst)]))
       (into {})
       (t/fn-t)))

(defmethod resolve-type* 'or [t subst]
  (->> t
       (t/or-types)
       (map #(resolve-type % subst))
       (t/or-t)
       ((fn [t]
          (if (t/or-t? t)
            (if (every? t/fn-t? (t/or-types t))
              (t/merge-fns (t/or-types t))
              t)
            t)))))

(defmethod resolve-type* 'and [t subst]
  (->> t
       (t/and-types)
       (map #(resolve-type % subst))
       (t/and-t)))

(defmethod resolve-type* 'class [t subst]
  (t/class-t (resolve-type (t/class-value t) subst)))

(defmethod resolve-type* 'maybe [t subst]
  (t/maybe-t (resolve-type (t/maybe-value t) subst)))

(defmethod resolve-type* 'value [t subst]
  (t/value-t (resolve-type (t/type-value t) subst)))

(defmethod unify-terms [#'number? #'integer?] [x y subst]
  subst)

;; (instrument-ns)
