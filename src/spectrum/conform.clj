(ns spectrum.conform
  (:require [clojure.core :as c]
            [clojure.data]
            [clojure.math.combinatorics :as combo]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.data :as data]
            [spectrum.java :as j]
            [spectrum.types :as t]
            [spectrum.util :refer [instrument-ns validate! defn-memo]])
  (:import [clojure.lang IPersistentMap IPersistentSet Sequential]))

;; inspired by:
;; https://eli.thegreenplace.net/2018/unification/
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
  "Does a occur anywhere inside b"
  [a b subst]
  ;; {:post [(do (when % (println "occurs?" a b "=>" %)) true)]}
  (cond
    (= a b) true
    (and (t/logic? b) (get subst b)) (occurs? a (get subst b) (dissoc subst b))
    (composite? b) (boolean (some (fn [b*]
                                    (occurs? a b* subst)) (seq b)))
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
(s/def ::substs (s/nilable (s/coll-of ::subst :kind sequential? :min-count 1)))

(defn unify-any-any [x y substs]
  ;; {:post [(do (println "unify any any" x y substs "=>" %) true)]}
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
     (when-let [ancestors (t/ancestors y)]
       (->> ancestors
            (some (fn [a]
                    (unify x a substs))))))))

(defmethod unify-terms [#'any? #'any?] [x y substs]
  (unify-any-any x y substs))

(s/fdef merge-substs-1 :args (s/cat :s ::substs) :ret ::subst)
(defn merge-substs-1 [substs]
  (->>
   substs
   (reduce (fn [final subst]
             (reduce (fn [final [k v]]
                       (update-in final [k] (fnil conj #{}) v)) final subst)) {})
   (reduce (fn [final [k v]]
             (assoc final k (t/or-t v))) {})))

(s/fdef merge-substs :args (s/cat :s ::substs) :ret ::substs)
(defn merge-substs
  [substs]
  [(merge-substs-1 substs)])

(defn cyclic-t? [t subst]
  (and (get subst t)
       ;; if it resolves to itself, it's cyclic
       (= t (resolve-type t subst))))

(defn free-t? [t subst]
  (and (t/logic? t)
       (or (not (get subst t))
           (cyclic-t? t subst))))

(defn narrow-unify-any-logic-1 [x y subst]
  (let [y* (get subst y)]

    ;;; unifying x and y, but: y is logic, it resolves to a value that
    ;;; is wider than x (such that it doesn't unify), but by narrowing the
    ;;; type more, we can make x and y unify

    (when-let [substs* (and (t/logic? y)
                            (not (free-t? y subst))
                            (not (seq (unify x y* [subst])))
                            (not (occurs? y x subst))
                            (unify x y [(dissoc subst y)]))]
      (let [subst* (-> substs* merge-substs-1)
            y** (resolve-type y subst*)]
        (when (and (unify y* y** [subst])
                   (not (unify y** y* [subst])))
          ;; (debug-substs y* substs*)
          ;; (debug-substs y** substs*)
          substs*)))))

(defn assoc-subst [subst x y]
  (when (occurs? x y subst)
    (println "assoc-substs warn" x "occurs?" y))
  (assoc subst x y))

(defn unify-any-logic-1 [x y subst]
  (cond
    (get subst y) (let [y* (get subst y)]
                    (or (when-not (cyclic-t? y* subst)
                          (unify x y* [subst]))
                        (narrow-unify-any-logic-1 x y subst)))
    (occurs? y x subst) (do (println "occurs?" y x) nil)
    (not (t/ignore? y)) [(assoc-subst subst y x)]
    :else [subst]))

(defn unify-logic-any-1 [x y subst]
  (cond
    (and (get subst x) (not (cyclic-t? x subst))) (unify (get subst x) y [subst])
    (occurs? x y subst) (do (println "occurs?" x y) nil)
    (not (t/ignore? x)) [(assoc-subst subst x y)]
    :else [subst]))

(defn unify-logic-any [x y substs]
  ;; {:post [(do (println "logic any" x y "=>" (boolean %)) true)]}
  ;; (println "logic any" x y)
  (some->> substs
           (mapcat (fn [s]
                     (unify-logic-any-1 x y s)))
           (filter identity)
           (seq)))

(defmethod unify-terms [#'t/logic? #'any?] [x y substs]
  (unify-logic-any x y substs))

(s/fdef unify-any-logic :args (s/cat :x any? :y any? :substs ::substs) :ret ::substs)
(defn unify-any-logic [x y substs]
  (some->> substs
           (mapcat (fn [s]
                     (unify-any-logic-1 x y s)))
           (filter identity)
           (seq)))

(defmethod unify-terms [#'any? #'t/logic?] [x y substs]
  (unify-any-logic x y substs))

(defn unify-logic-logic-1 [x y subst]
  (cond
    (= x y) [subst]
    (and (free-t? x subst) (free-t? y subst)) [(assoc-subst subst y x)]
    (and (free-t? y subst)) [(assoc-subst subst y x)]
    (and (free-t? x subst)) [(assoc-subst subst x y)]
    :else (or (unify (get subst x) (get subst y) [subst])
              (unify-any-logic-1 x y subst))))

(defmethod unify-terms [#'t/logic? #'t/logic?] [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-logic-logic-1 x y s)))
       (filter identity)
       (seq)))

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

(def ^:dynamic *unify-temp-cache* nil)

(defn with-ensure-temp-cache [unify-f]
  (fn [& args]
    (if-not *unify-temp-cache*
      (binding [*unify-temp-cache* (atom {})]
        (apply unify-f args))
      (apply unify-f args))))

(defn cacheable? [x y]
  (and (= #{} (t/get-lvars x))
       (= #{} (t/get-lvars y))))

;;; two cache levels. One of just [x y], which is persistent across
;;; calls to unify, only used when no logic vars present. second
;;; level, [x y substs] only present in the stack of a single
;;; top-level unify call

(defn with-perm-cache [unify-f]
  (let [cache (atom {})]
    (fn
      ([x y]
       (unify-f x y))
      ([x y substs]
       (if-let [[k ret] (find @cache [x y])]
         (if ret
           substs
           nil)
         (if-let [ret (unify-f x y substs)]
           (if (cacheable? x y)
             (do
               (swap! cache assoc [x y] (boolean ret))
               substs)
             ret)))))))

(defn pending? [x]
  (instance? clojure.lang.IPending x))

(defn with-temp-cache [unify-f]
  (fn [x y substs]
    (let [k [x y substs]]
      (if-let [[_ ret] (find @*unify-temp-cache* k)]
        (do
          (when (and (pending? ret) (not (realized? ret)))
            (println "with-temp unrealized key:" x y substs)
            (assert false))
          ret)
        (let [_ (swap! *unify-temp-cache* assoc k (promise))
              ret (unify-f x y substs)]
          (swap! *unify-temp-cache* assoc k ret)
          ret)))))

(def ^:dynamic *unify-seen* [])

(def ^:dynamic *unify-call-count* nil)

(defn with-detect-loop [unify-f]
  (fn [x y substs]
    (try
      (when-let [[_ _  seen-substs] (->> *unify-seen* (filter #(= [x y substs] %)) first)]
        (println "depth:" (count *unify-seen*))
        ;; (debug-substs x substs)
        ;; (debug-substs y substs)
        (println "seen!" x y (vec (take 2 (clojure.data/diff substs seen-substs))))
        ;; (last args)
        (assert false)
        )
      (binding [*unify-seen* (conj *unify-seen* [x y substs])]
        (unify-f x y substs)))))

(defn with-unify-call-count [unify-f]
  (fn [x y substs]
    (if (nil? *unify-call-count*)
      (binding [*unify-call-count* (atom 1)]
        (unify-f x y substs))
      (do
        (swap! *unify-call-count* inc)
        (unify-f x y substs)))))

(defn with-no-infinite [unify-f]
  (fn [x y substs]
    (when (> @*unify-call-count* 10000)
      (assert false))
    (when (= 0 (mod @*unify-call-count* 100))
      (println "call count" @*unify-call-count*))
    (unify-f x y substs)))

(defn with-canonical [unify-f]
  (fn [x y substs]
    (unify-f (t/canonicalize x) (t/canonicalize y) substs)))

(defn with-class-cast [unify-f]
  (fn [x y substs]
    (or (unify-f x y substs)
        (let [cx (t/class-cast x)
              cy (t/class-cast y)]
          (when (or cx cy)
            (let [ret (unify-f (or cx x) (or cy y) substs)]
              (when ret
                ;; (println "with-class-cast" (or cx x) (or cy y) "=>" ret) true)
              ret)))))))

(defn with-disentangle [unify-f]
  (fn [x y substs]
    (let [ys (disentangle y)
          substs (->> ys
                      (map (fn [y]
                             (seq (unify-f x y substs))))
                      (doall))]
      (when (every? seq substs)
        (->> substs
             (apply concat)
             (filter identity)
             distinct
             seq)))))

(defn with-depth [unify-f]
  (fn [& args]
    (println "unify depth:" (count *unify-seen*))
    (apply unify-f args)))

(defn with-debug [unify-f]
  (fn [& args]
    (let [[x y substs] args
          x-lvars (t/get-lvars x)
          y-lvars (t/get-lvars y)
          lvars (set/union x-lvars y-lvars)
          subst (merge-substs-1 substs)]
      (when substs
        (println "unify pre" x y ":" (->> lvars
                                          (map (fn [l]
                                                 (let [r (get subst l l)]
                                                   (if (not= l r)
                                                     [l r]
                                                     [l :free]))))
                                          (into {}))))
      (let [ret (apply unify-f args)]
        (println "unify post" x y "=>" ret)
        ret))))

(defn with-require-substs
  "It's easy to accidentally call the 2-arity unify from inside
  unify-terms, which can cause serious, hard-to-find bugs. Assert that
  never happens"
  [unify-f]
  (fn
    ([x y]
     (assert (= [] *unify-seen*))
     (unify-f x y [{}]))
    ([x y substs]
     (unify-f x y substs))))

(defn with-doall [unify-f]
  (fn [& args]
    (->> (apply unify-f args)
         (seq))))

(defn unify*
  ([x y]
   (unify* x y [{}]))
  ([x y substs]
   (assert substs)
   (cond
     (= x y) substs
     :else (unify-terms x y substs))))

(s/fdef unify :args (s/cat :x any? :y any? :substs (s/? ::substs)) :ret ::substs)
(def unify
  "Unifies term x and y with initial subst.

    Returns a seq of subst maps, (map of name->term) that unify x and y, or nil if
    they can't be unified."
  (-> unify*
      ;; with-debug
      ;; with-depth
      with-doall
      with-disentangle
      with-no-infinite
      with-unify-call-count
      with-temp-cache
      with-perm-cache
      with-class-cast
      with-canonical
      with-ensure-temp-cache
      with-require-substs))

(defn debug-substs
  "Given a subst, print the parts relevant to type t"
  [t substs]
  (println "debug-relevant" t "relevant subst:" (->> substs
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

(defmethod first-t :default [x]
  (println "first-t: can't first" x)
  (assert false))

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
  {:post [(validate! (s/nilable (s/coll-of t/value-t?)) %)]}
  (let [val (t/type-value val-t)]
    (when (and (seqable? val) (seq val))
      [(t/value-t (first val))])))

(s/def :dx/state (s/nilable ::t/type))
(s/def ::dx-ret (s/keys :req-un [:dx/state ::substs]))

(s/def ::dx-rets (s/nilable (s/coll-of ::dx-ret)))

(defmethod dx :default [x y substs]
  {:post [(validate! ::dx-rets %)]}
  (when-let [substs* (unify x y substs)]
    [{:state nil :substs substs*}]))

(defmethod dx 'cat [cat-x y substs]
  {:post [(validate! ::dx-rets %)]}
  (let [substs-orig substs
        [x & xr :as xs] (t/cat-types cat-x)]
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
         (filter identity)
         (seq))))

(defmethod dx 'seq-of [seq-x y substs]
  {:post [(validate! ::dx-rets %)]}
  (let [x (t/seq-value seq-x)
        substs-orig substs]
    (cond
      (nil? y) [{:state nil :substs substs}]
      (= y x) [{:state nil :substs substs}
               {:state seq-x :substs substs}]
      (t/logic? y) (when-let [substs (unify-any-logic seq-x y substs)]
                     [{:state nil :substs substs}
                      {:state seq-x :substs substs}])
      :else (when-let [substs (unify x y substs)]
              [{:state nil :substs substs}
               {:state seq-x :substs substs}]))))

(defmethod dx 'alt [alt-x y substs]
  (->> (t/alt-types alt-x)
       (mapcat (fn [at]
                 (dx at y substs)))))

(defmethod dx 'value [val-x y substs]
  {:post [(validate! ::dx-rets %)]}
  (let [val (t/type-value val-x)]
    (->>
     [(when-let [substs* (unify val-x y substs)]
        [{:state nil :substs substs*}])
      (when (and (seqable? val) (seq val))
        (let [[v & vr] val
              substs (unify (t/value-t v) y substs)]
          (when (seq substs)
            [{:state (when (seq vr)
                       (t/value-t (seq vr))) :substs substs}])))]
     (apply concat))))

(defn unify-dx-dx [tx ty substs]
  ;; {:pre [(do (println "unify dx dx pre" tx ty) true)]
  ;;  :post [(do (println "unify dx dx post" tx ty "=>" %) true)]}
  (let [ys (first-t ty)]
    (or
     (some->> ys
              (mapcat (fn [y]
                        (let [dx-rets (dx tx y substs)]
                          (->> dx-rets
                               (mapcat (fn [dx-ret]
                                         (let [{dx-x :state substs* :substs} dx-ret
                                               substs substs*
                                               dy-rets (dx ty y substs)]
                                           (->> dy-rets
                                                (mapcat (fn [dy-ret]
                                                        (let [{dy-y :state substs :substs} dy-ret]
                                                          (->>
                                                           [(when (and substs
                                                                       (or (not= tx dx-x)
                                                                           (not= ty dy-y)))
                                                              (unify dx-x dy-y substs))]
                                                           (apply concat)))))))))))))
              (distinct)
              (seq))
     (when (and (accept-nil? tx) (nil? (first-t ty)))
       substs))))

(defmethod unify-terms [#'dx? #'dx?] [tx ty substs]
  (unify-dx-dx tx ty substs))

(defmethod unify-terms [#'dx? 'value] [x y substs]
  {:post [(validate! ::substs %)]}
  (let [val (t/type-value y)]
    (when (and (seqable? val) (seq val))
      ;; spec-t?
      (unify-dx-dx x (t/cat-t (map t/value-t val)) substs))))

(defmethod unify-terms ['seq-of 'seq-of] [x y substs]
  ;; can't use dxdx here, because both could accept nil, and [seq-of a?] [seq-of b?] shouldn't unify
  (unify (t/type-value x) (t/type-value y) substs))

(defmethod unify-terms ['seq-of #'t/logic?] [x y substs]
  ;; use this to short-circuit
  (if (= (t/type-value x) y)
    substs
    (unify-any-logic x y substs)))

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

(defmethod unify-terms ['or #'any?] [x y substs]
  (if (every? (fn [s] (occurs? y x s)) substs)
    substs
    (->> (t/or-types x)
         (mapcat (fn [x]
                   (unify x y substs)))
         (filter identity)
         (distinct)
         (doall)
         (seq))))

(defn unify-any-or [x y substs]
  (let [rets (->> (t/or-types y)
                  (combo/subsets)
                  (drop 1)
                  (butlast)
                  (mapcat (fn [y*]
                            (unify x (t/or-t y*) substs)))
                  (distinct))]
    (when (every? seq rets)
      rets)))

(defmethod unify-terms [#'any? 'or] [x y substs]
  (unify-any-or x y substs))

(defmethod unify-terms ['or 'or] [x y substs]
  (unify-any-or x y substs))

(defmethod unify-terms [#'any? 'and] [x y substs]
  (->> (t/type-value y)
       (some (fn [y*]
               (unify x y* substs)))
       (filter identity)
       seq))

(defmethod unify-terms ['and #'any?] [x y substs]
  (reduce (fn [substs x*]
            (when substs
              (unify x* y substs))) substs (t/type-value x)))

(defmethod unify-terms ['and 'and] [x y substs]
  (let [ys (-> y t/type-value set)]
    (reduce (fn [substs x*]
              (when substs
                (or
                 (when (contains? ys x*)
                   substs)
                 (->> ys
                      (some (fn [y*]
                              (unify x* y* substs))))))) substs (t/type-value x))))

(defmethod unify-terms ['not #'any?] [x y substs]
  (when-not (unify (t/type-value x) y substs)
    substs))

(defmethod unify-terms ['not 'not] [x y substs]
  (if-let [substs (unify (t/type-value x) (t/type-value y) substs)]
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
  (let [cx (t/type-value x)
        cy (t/type-value y)]
    (cond
      (and (class? cx) (class? cy) (isa? cy cx)) substs
      :else (unify cx cy substs))))

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
      (and (nil? (seq val)) (not= nil val))
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
         [(t/or-t ts) (merge-substs-1 substs)]))))))

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
  (assert false))

(defmethod unify-terms ['invoke #'any?] [invoke-x y subst]
  {:post [(do (println "unify terms invoke any:" invoke-x y "=>" %) true)]}
  (assert false))

(defmethod unify-terms ['spec 'spec] [x y substs]
  (unify-terms (t/type-value x) (t/type-value y) substs))

(defmethod unify-terms ['spec 'value] [x y substs]
  (let [yv (t/type-value y)]
    (when (coll? yv)
      (unify x (t/spec-t (t/cat-t (map t/value-t yv))) substs))))

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
       (filter symbol?)
       distinct
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
  {:post [(validate! ::substs %)]}
  (let [val (t/type-value y)
        spread (when (and (seqable? val) (seq val))
                 (t/spec-t (t/cat-t (map t/value-t val))))]
    (->> [(when (and (contains? @value-pred-whitelist x) (x val))
            substs)
          (when spread
            (unify x spread substs))]
         (apply concat)
         (seq))))

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

(defmethod unify-terms ['class 'value] [x v substs]
  {:post [(validate! ::substs %)]}
  (let [cls (t/type-value x)
        val (t/type-value v)]
    (or
     (when (t/logic? cls)
       (unify-logic-any cls val substs))
     (when (instance? cls val)
       substs))))

(defmethod unify-terms ['value 'value] [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

;; TODO ideally order shouldn't matter?
(prefer-method unify-terms [#'any? #'t/logic?] [#'any? #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] [#'t/logic? #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['not #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['spec #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['value #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['and #'any?])
(prefer-method unify-terms [#'any? 'and] ['or #'any?] )
(prefer-method unify-terms [#'any? 'and] ['sequential #'any?])
(prefer-method unify-terms [#'any? 'and] ['value #'any?])
(prefer-method unify-terms [#'any? 'and] ['and #'any?])
(prefer-method unify-terms [#'any? 'value] ['and #'any?])
(prefer-method unify-terms [#'any? 'invoke] ['or #'any?])
(prefer-method unify-terms [#'any? 'invoke] ['value #'any?])
(prefer-method unify-terms [#'any? 'not] ['or #'any?] )
(prefer-method unify-terms [#'any? 'not] ['value #'any?])
(prefer-method unify-terms [#'any? 'value] [#'sequential? #'any?])
(prefer-method unify-terms [#'any? 'value] [#'t/logic? #'any?])
(prefer-method unify-terms [#'any? 'value] ['sequential #'any?])
(prefer-method unify-terms [#'dx? #'dx?] [#'any? 'value])
(prefer-method unify-terms [#'dx? #'dx?] ['value #'any?])
(prefer-method unify-terms [#'dx? 'value] [#'dx? #'dx?])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? #'any?])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'and])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'invoke])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'not])
(prefer-method unify-terms [#'t/logic? #'any?] [#'any? 'or])
(prefer-method unify-terms ['alt #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['invoke #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['invoke #'any?] [#'any? 'value])
(prefer-method unify-terms ['not #'any?] [#'any? 'and])
(prefer-method unify-terms ['not #'any?] [#'any? 'value])
(prefer-method unify-terms ['or #'any?] [#'any? #'t/logic?])
(prefer-method unify-terms ['or #'any?] [#'any? 'value])
(prefer-method unify-terms [#'any? 'or] ['or #'any?])

(defn resolve-type-dispatch [t subst]
  (t/type-tag t))

(defmulti resolve-type* #'resolve-type-dispatch)

(defmethod resolve-type* :default [t subst]
  t)

(def ^:dynamic *resolve-seen* #{})

(s/fdef resolve-type :args (s/cat :t any? :s (s/nilable ::subst)) :ret any?)
(defn resolve-type
  [t subst]
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

(defmethod resolve-type* 'seq-of [t subst]
  (t/seq-of (resolve-type (t/type-value t) subst)))

(defmethod resolve-type* 'invoke [t subst]
  {:post [(do (println "resolve invoke" t subst "=>" %) true)]}
  (apply t/invoke-t (map (fn [t] (resolve-type t subst)) (t/type-values t))))

(defn recursive-type? [t subst]
  (let [t-lvars (t/get-lvars t)
        t* (resolve-type t subst)
        t*-lvars (t/get-lvars t*)
        ret (and t*
                 (not= t t*)
                 (->> (set/intersection t-lvars t*-lvars)
                      (remove (fn [t]
                                (free-t? t subst)))
                      (seq)
                      (boolean)))]
    ret))

(instrument-ns)
