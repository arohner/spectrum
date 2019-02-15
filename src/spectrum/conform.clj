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

(defn composite? [x]
  (cond
    (t/logic? x) false
    (coll? x) true))

(s/fdef occurs? :args (s/cat :x ::t/type :y any? :s ::subst) :ret boolean?)
(defn occurs?
  "Does v occur anywhere inside typ"
  [x y subst]
  (cond
    (= x y) true
    (and (t/logic? y) (get subst y)) (recur x (get subst y) (dissoc subst y))
    (composite? y) (boolean (some (fn [y*]
                                    (occurs? x y* subst)) (seq y)))
    :else false))

(defn dx-dispatch [x y substs]
  (t/type-tag x))

(defmulti dx
  #'dx-dispatch
  :default :default)

(declare unify-terms-dispatch)

(ns-unmap 'spectrum.conform 'unify-terms)

(defmulti unify-terms "" #'unify-terms-dispatch :hierarchy t/types-hierarchy :default [#'any? #'any?])

(defn-memo unify-terms-methods []
  (-> unify-terms .getMethodTable keys set))

(defn-memo dx-methods []
  (-> dx .getMethodTable keys set))

(defn dx? [t]
  (contains? (dx-methods) (t/type-tag t)))

(defn var-pred? [x]
  (and (var? x)
       (-> x .sym t/predicate-symbol?)))

(defn unify-term-value [x]
  (cond
    (t/logic? x) #'t/logic?
    (t/value-t? x) 'value
    (t/tagged? x) (if (t/parents x)
                    (t/type-tag x)
                    #'any?)
    (var? x) (if (t/parents x)
               x
               #'any?)
    (nil? x) nil
    (sequential? x) 'sequential
    (set? x) 'set
    (map? x) 'map
    :else #'any?))

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

(defmethod unify-terms [#'any? #'any?] [x y substs]
  (or
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
                    (unify x a substs))))))))

(s/fdef merge-substs :args (s/cat :s ::substs) :ret ::subst)
(defn merge-substs [substs]
  (->>
   substs
   (reduce (fn [final subst]
             (reduce (fn [final [k v]]
                       (update-in final [k] (fnil conj #{}) v)) final subst)) {})
   (reduce (fn [final [k v]]
             (assoc final k (t/or-t v))) {})))

(defn narrow-unify-logic-any-1 [x y subst]
  ;;; unify x and y, x is logic. y unifies, but x's subst is currently
  ;;; wider than what y accepts, so x's subst must become narrower
  (when-let [substs (and (t/logic? x)
                        (get subst x)
                        (unify (get subst x) y [subst]))]
    (let [subst (merge-substs substs)
          y-substs (unify x y [(dissoc subst x)])
          y-subst (merge-substs y-substs)
          x* (resolve-type x y-subst)]
      (assert x*)
      (when-not (seq (unify x* (resolve-type x subst)))
        y-substs))))

(defn narrow-unify-any-logic-1 [x y subst]
  (let [y* (get subst y)]

    ;;; unifying x and y, but: y is logic, it resolves to a value,
    ;;; that value doesn't unify with x, but by narrowing the type
    ;;; more, we can make x and y unify

    (when-let [substs* (and (t/logic? y)
                            (not (t/logic? y*))
                            (not (seq (unify x y* [subst])))
                            (not (occurs? y x subst))
                            (unify x y [(dissoc subst y)]))]
      (let [subst* (merge-substs substs*)
            y** (resolve-type y subst*)]
        (when (unify y* y** substs*)
          substs*)))))

(defn unify-any-logic-1 [x y subst]
  (cond
    (get subst y) (let [y* (get subst y)]
                    (or (unify x y* [subst])
                        (narrow-unify-any-logic-1 x y subst)))
    (occurs? y x subst) nil
    (not (t/ignore? y)) [(assoc subst y x)]
    :else [subst]))

(defn unify-logic-any-1 [x y subst]
  (cond
    (get subst x) (or
                   (narrow-unify-logic-any-1 x y subst)
                   (unify (get subst x) y [subst]))
    (occurs? x y subst) nil
    (not (t/ignore? x)) [(assoc subst x y)]
    :else [subst]))

(defn unify-logic-any [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-logic-any-1 x y s)))
       (filter identity)))

(defmethod unify-terms [#'t/logic? #'any?] [x y substs]
  (unify-logic-any x y substs))

(defmethod unify-terms [#'any? #'t/logic?] [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-any-logic-1 x y s)))
       (filter identity)))

(defmethod unify-terms ['sequential #'any?] [x y subst]
  (when (and (seqable? y) (seq y))
    (some->> subst
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defmethod unify-terms ['set #'any?] [x y subst]
  (when (and (seqable? y) (seq y))
    (some->> subst
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defmethod unify-terms ['map 'map] [x y subst]
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

(defmulti disentangle* #'t/type-tag)

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

(defn unify-canonical [x y substs]
  ;; {:post [(validate! ::substs %)]}
  (let [x (t/canonicalize x)
        y (t/canonicalize y)
        ys (disentangle y)
        substs (map (fn [y]
                      (unify-terms x y substs)) ys)]
    (when (every? seq substs)
      (->> substs
           (apply concat)
           (filter identity)
           distinct
           seq))))

(defn unify-class [x y]
  (let [x* (t/class-cast x)
        y* (t/class-cast y)]
    (when (and x* y* (->> (unify-terms x* y* [{}])
                          (filter identity)
                          distinct
                          seq))
      [{}])))

(defn cacheable? [x y]
  (and (= #{} (t/get-lvars x))
       (= #{} (t/get-lvars y))))

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
   {
    ;; :pre [(do (println "unify pre" x y substs) true])
    ;; :post [(do (println "unify" x y substs "=>" %) (when (> (count %) 1) (println "unify" x y "multiple ret" %)) true)]
    }
   (assert substs)
   (cond
     (= x y) substs
     (cacheable? x y) (when (unify-cache x y)
                        substs)
     :else (unify-canonical x y substs))))

(defn debug-substs
  "Given a subst, print the parts relevant to type t"
  [t substs]
  (println "debug-relevant" t "subst:" (->> substs
                                            (map (fn [s]
                                                   (select-keys s (t/get-lvars t))))
                                            (filter identity)
                                            (distinct))))

(defn debug-unify
  ([x y])
  ([x y substs]
   (let [ret (unify x y substs)]
     (println "debug-unify" x y "=>" (boolean (seq ret)))
     (debug-substs x substs)
     (debug-substs y substs)
     ret)))

(defmulti accept-nil?
  "True if this (regex) type may accept no input"
  #'t/type-tag
  :default nil)

(defmethod accept-nil? nil [_]
  false)

(defn valid? [x y]
  (boolean (seq (unify x y))))

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

(defmethod first-t 'value [val-t]
  (let [val (t/type-value val-t)]
    (when (and (seqable? val) (seq val))
      [(t/value-t (first val))])))

(s/def :dx/state (s/nilable ::t/type))
(s/def ::dx-ret (s/keys :req-un [:dx/state ::substs]))

(s/def ::dx-rets (s/nilable (s/coll-of ::dx-ret)))

(defmethod dx :default [x y substs]
  {:post [(validate! ::dx-rets %)]}
  (when-let [substs (unify x y substs)]
    [{:state nil :substs substs}]))

(defmethod dx 'cat [cat-x y substs]
  {:post [(validate! ::dx-rets %)]}
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

(defmethod dx 'seq-of [seq-x y substs]
  {:post [(validate! ::dx-rets %)]}
  (let [x (t/seq-value seq-x)]
    (or
     (when-let [substs (unify seq-x y substs)]
       [{:state nil :substs substs}])
     (when-let [substs (unify x y substs)]
       [{:state nil :substs substs}
        {:state seq-x :substs substs}]))))

(defmethod dx 'alt [alt-x y substs]
  (->> (t/alt-types alt-x)
       (mapcat (fn [at]
                 (dx at y substs)))))

(defmethod dx 'value [val-x y substs]
  {:post [(validate! ::dx-rets %)]}
  (let [val (t/type-value val-x)]
    (when (seqable? val)
      (if (seq val)
        (let [[v & vr] val
              substs (unify v y substs)]
          (when (seq substs)
            [{:state (when (seq vr)
                       (t/value-t (seq vr))) :substs substs}]))
        nil))))

(defn unify-dx-dx [tx ty substs]
  (let [ys (first-t ty)]
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
                                                                  (or (not= tx dx-x)
                                                                      (not= ty dy-y)))
                                                         (unify dx-x dy-y substs))]
                                                      (apply concat))))))))))))
         (distinct))))

(defmethod unify-terms ['seq-of 'seq-of] [x y substs]
  ;; can't use dxdx here, because both could accept nil, and [seq-of a?] [seq-of b?] shouldn't unify
  (unify (t/type-value x) (t/type-value y) substs))

(defmethod disentangle* :default [t]
  [t])

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

(defmethod unify-terms [#'dx? #'dx?] [tx ty substs]
  (unify-dx-dx tx ty substs))

(defmethod unify-terms [#'dx? nil] [x y substs]
  (when (accept-nil? x)
    substs))

(defmethod unify-terms [nil #'dx?] [x y substs]
  (when (accept-nil? y)
    substs))

(defmethod unify-terms [nil nil] [x y substs]
  substs)

(defmethod unify-terms ['coll-of 'coll-of] [a b subst]
  (let [x (t/type-value a)
        y (t/type-value b)]
    (unify x y subst)))

(defmethod unify-terms ['or #'any?] [or-x y substs]
  (->> (t/or-types or-x)
       (mapcat (fn [x]
                 (unify x y substs)))))

(defmethod unify-terms ['or 'or] [or-x or-y substs]
  (->> or-y
       (t/or-types)
       (seq)
       (combo/permutations)
       (mapcat (fn [ys]
                 (reduce (fn [substs y]
                           (when substs
                             (unify or-x y substs))) substs ys)))))

(defmethod unify-terms [#'any? 'and] [x y substs]
  ;; {:post [(do (println "unify-terms any and" x y "=>" %) true)]}
  (->> (t/type-value y)
       (mapcat (fn [y]
                 ;; {:post [(do (println "unify any and" x y "->" (boolean (seq %))) true)]}
                 (when-not (and (t/not-t? y)
                                (unify x (t/type-value y)))
                   (unify x y substs))))
       (filter identity)))

(defmethod unify-terms ['and 'and] [x y substs]
  (let [xss (combo/permutations (t/type-value x))
        yss (combo/subsets (seq (t/type-value y)))]
    (->> yss
         (mapcat (fn [ys]
                   (reduce (fn [substs xs]
                             (reduce (fn [substs x]
                                       (when substs
                                         (unify x (t/and-t ys) substs))) substs xs)) substs xss))))))

(defmethod unify-terms ['not #'any?] [x y substs]
  (when-not (unify (t/type-value x) y substs)
    substs))

(defmethod unify-terms ['not 'not] [x y substs]
  (if-let [substs (unify (t/type-value x) (t/type-value y))]
    substs
    nil))

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

(defmethod accept-nil? 'alt [t]
  (some nil? (t/alt-types t)))

(defmethod accept-nil? 'seq-of [t]
  true)

(defmethod accept-nil? 'cat [t]
  (every? accept-nil? (t/cat-types t)))

(defmethod accept-nil? 'value [t]
  (let [val (-> t t/type-value)]
    (if (seqable? val)
      (nil? (seq val))
      false)))

(defn apply-invoke-dispatch [it subst]
  (let [f (t/type-value it)]
    (cond
      (t/tagged? f) (t/type-tag f)
      (keyword? f) :keyword
      (var? f) #'var?)))

(defmulti apply-invoke #'apply-invoke-dispatch)

(s/def ::apply-invoke-ret (s/nilable (s/coll-of (s/tuple ::t/type ::subst))))

(s/fdef apply-invoke :args (s/cat :it t/invoke-t? :s ::subst))
(defmethod apply-invoke :default [it subst]
  {:post [(validate! ::apply-invoke-ret %)]}
  (println "apply-invoke :default" it)
  [[it subst]])

(defn printable-invoke-t [it]
  (if-let [v (-> it (nth 1) meta :var)]
    (assoc it 1 v)
    it))

(defmethod apply-invoke 'fn [it subst]
  {
   ;; :post [(do (println "apply-invoke:" it substs "=>" %) true)]
   :post [(validate! ::apply-invoke-ret %)]
   }
  (let [[f invoke-args] (t/type-values it)
        fn-args (t/fn-args f)
        fn-ret (t/fn-ret f)]
    ;; (println "apply invoke" fn-args invoke-args (boolean (seq (debug-unify fn-args invoke-args substs))))
    (when-let [aggregate-substs (seq (unify fn-args invoke-args [subst]))]
      ;; a fn of {a b, c d} could be invoked with (or a c). If we
      ;; examine arities individually, we could fail all of them, so also check the aggregate case
      (or
       (->> (nth f 1)
            (mapcat (fn [[f-args f-ret]]
                      (let [substs (seq (unify f-args invoke-args [subst]))]
                        (some->> substs
                                 (map (fn [subst]
                                        {:post [(do (println "apply invoke fn" f invoke-args "=>" %) true)]}
                                        [(resolve-type f-ret subst) subst]))))))
            (filter identity)
            (distinct)
            (doall)
            (seq))
       (->> aggregate-substs
            (map (fn [s]
                   [(resolve-type fn-ret s) s])))))))

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

(s/fdef thunk :args (s/cat :it t/invoke-t? :s (s/? ::substs)) :ret (s/nilable (s/tuple ::t/type ::subst)))
(defn thunk
  ([it]
   (thunk it [{}]))
  ([it substs]
   {:post [(do (println "thunk" it "=>" %) true)]}
   (some->>
    substs
    (mapcat (fn [s] (apply-invoke it s)))
    ((fn [xs]
       (let [ts (map first xs)
             substs (map second xs)]
         (println "thunk: apply-invoke" it "=>" ts substs)
         (assert substs)
         [(t/or-t ts) (merge-substs substs)]))))))

(s/fdef maybe-thunk :args (s/cat :it t/invoke-t? :s (s/? ::substs)) :ret (s/nilable (s/tuple ::t/type ::subst)))
(defn maybe-thunk
  "Thunk if possible, else return the invoke-t"
  ([it]
   (maybe-thunk it [{}]))
  ([it substs]
   (or (thunk it substs)
       it)))

(defn apply-t
  "Utility/test fn. Given an invoke, return all possible return types"
  [f args]
  (-> (t/invoke-t f (t/maybe-cat args))
      (thunk)))

(defmethod unify-terms [#'any? 'invoke] [x invoke-y subst]
  {:post [(do (println "unify terms any invoke:" x invoke-y "=>" %) true)]}
  (assert false)
  ;; (->> (apply-invoke invoke-y subst)
  ;;      (mapcat (fn [[y subst]]
  ;;                {:post [(do (println "unify terms any invoke" x y "->" %) true)]}
  ;;                (unify x y [subst]))))
  )

(defmethod unify-terms ['invoke #'any?] [invoke-x y subst]
  {:post [(do (println "unify terms invoke any:" invoke-x y "=>" %) true)]}
  (assert false)
  ;; (->>
  ;;  (apply-invoke invoke-x subst)
  ;;  (mapcat (fn [[x* subst]]
  ;;            (unify x* y [subst]))))
  )

(defmethod unify-terms ['spec #'any?] [x y substs]
  (unify-terms (t/type-value x) y substs))

(defmethod unify-terms [#'any? 'spec] [x y substs]
  (unify-terms x (t/type-value y) substs))

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

(t/derive-type #'any? #'t/logic?)

(derive-all-any)
(t/derive-type #'any? #'dx?)

(doseq [m (-> (dx-methods) (disj :default))]
  (t/derive-type #'dx? m))

(def value-pred-whitelist (atom #{}))

(s/fdef add-value-pred-whitelist! :args (s/cat :v var?))
(defn add-value-pred-whitelist!
  "Declare var predicate v as safe for calling to unify with values. v
  should be a predicate, pure (free of side-effects) and fast"
  [v]
  (swap! value-pred-whitelist conj v))

(doseq [v (t/core-predicates)]
  (add-value-pred-whitelist! v))

(defmethod unify-terms [#'any? 'value] [x y substs]
  (let [val (t/type-value y)]
    (->> [(when (and (contains? @value-pred-whitelist x) (x val))
            substs)
          (unify x val substs)]
         (apply concat))))

(defmethod unify-terms [#'t/logic? 'value] [x y substs]
  (let [val (t/type-value y)]
    (unify-logic-any x y substs)))

(defn arities-complementary?
  "True if x and y are both fn-ts, and they have no arities in common"
  [x y]
  (->> y
       (t/type-value)
       (every? (fn [[y-args y-ret]]
                 (->> x
                      (t/type-value)
                      (every? (fn [[x-args x-ret]]
                                (not (unify x-args y-args)))))))))

(defn unify-merge-logic-fn-1
  "While attempting to unify two fn-ts, merge the right arity into the left fn, if possible"
  [x y subst]
  (let [x* (get subst x)]
    (when (and (t/logic? x)
               x*
               (t/fn-t? x*)
               (arities-complementary? x* y))
      (println "unify-merge-logic-fn" x* y)
      (assoc subst x (t/merge-fns [x* y])))))

(defn unify-merge-logic-fn [x y substs]
  (->> substs
       (map (fn [s]
              (unify-merge-logic-fn-1 x y s)))
       (filter identity)
       seq))

(defmethod unify-terms [#'t/logic? 'fn] [x y substs]
  (or (unify-merge-logic-fn x y substs)
      (unify-logic-any x y substs)))

(defmethod unify-terms ['fn 'fn] [x y substs]
  (->> x
       (t/type-value)
       (mapcat (fn [[x-args x-ret]]
                 (->> y
                      (t/type-value)
                      (mapcat (fn [[y-args y-ret]]
                                (some->> substs
                                         (unify x-ret y-ret)
                                         (unify x-args y-args)
                                         seq))))))
       seq))

(defmethod unify-terms ['value #'any?] [x y substs]
  (let [val (t/type-value x)]
    (unify val y substs)))

(defmethod unify-terms ['class 'value] [x v substs]
  (let [cls (t/type-value x)
        val (t/type-value v)]
    (or
     (when (t/logic? cls)
       (unify cls val substs))
     (when (instance? cls val)
       substs))))

(defmethod unify-terms [#'dx? 'value] [x y substs]
  (unify-dx-dx x y substs))

(defmethod unify-terms ['value 'value] [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(prefer-method unify-terms [#'t/logic? #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] [#'any? #'any?])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'invoke])
(prefer-method unify-terms [#'any? 'invoke] ['or #'any?])
(prefer-method unify-terms [#'any? 'invoke] ['value #'any?])
(prefer-method unify-terms [#'any? 'spec] [#'t/logic? #'any?])
(prefer-method unify-terms [#'any? 'value] [#'sequential? #'any?])
(prefer-method unify-terms [#'any? 'value] [#'t/logic? #'any?])
(prefer-method unify-terms ['alt #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['invoke #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['invoke #'any?] [#'any? 'value])
(prefer-method unify-terms ['or #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['or #'any?] [#'any? 'value])
(prefer-method unify-terms ['spec #'any?] [#'any? 'spec])
(prefer-method unify-terms ['spec #'any?] [#'any? 'value])
(prefer-method unify-terms [#'any? #'t/logic?] ['value #'any?])
(prefer-method unify-terms [#'dx? #'dx?] ['value #'any?])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'and])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'not])
(prefer-method unify-terms [#'any? #'t/logic?] ['not #'any?])
(prefer-method unify-terms ['not #'any?] [#'any? 'value])
(prefer-method unify-terms ['or #'any?] [#'any? 'and])
(prefer-method unify-terms [#'any? 'value] ['sequential #'any?])
(prefer-method unify-terms [#'dx? #'dx?] [#'any? 'value])
(prefer-method unify-terms ['spec #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms [#'any? 'not] ['value #'any?])
(prefer-method unify-terms ['or #'any?] [#'any? 'not])
(prefer-method unify-terms [#'any? 'and] ['value #'any?])

(defn resolve-type-dispatch [t subst]
  (t/type-tag t))

(defmulti resolve-type* #'resolve-type-dispatch)

(defmethod resolve-type* :default [t subst]
  t)

(def ^:dynamic *resolve-seen* #{})
(s/fdef resolve-type :args (s/cat :t any? :s (s/nilable ::subst)) :ret any?)
(defn resolve-type [t subst]
  (if-not (contains? *resolve-seen* t)
    (binding [*resolve-seen* (conj *resolve-seen* t)]
     (let [t* (get subst t t)]
        (cond
          (and (t/logic? t*) (not= t t*)) (resolve-type t* subst)
          :else (or (resolve-type* t* subst) t*))))
    t))

(defmethod resolve-type* 'cat [t subst]
  (when-not (every? identity (map #(resolve-type % subst) (t/cat-types t)))
    (println "resolve" t subst "=>" (map #(resolve-type % subst) (t/cat-types t))))
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
       (filter identity)
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

(defmethod resolve-type* 'invoke [t subst]
  {:post [(do (println "resolve invoke" t subst "=>" %) true)]}
  (apply t/invoke-t (map (fn [t] (resolve-type t subst)) (t/type-values t)))
  ;; (let [it
  ;;       [ret subst] (maybe-thunk it [subst])]
  ;;   (println "resolve ret" ret subst)
  ;;   (if (t/invoke-t? ret)
  ;;     ret
  ;;     (resolve-type ret subst)))
  )

(instrument-ns)
