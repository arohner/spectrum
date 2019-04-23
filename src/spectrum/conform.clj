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
            [spectrum.util :refer [instrument-ns validate! defn-memo debug-multimethod-dispatch]])
  (:import [clojure.lang IPersistentMap IPersistentSet Sequential]))

;; inspired by:
;; https://eli.thegreenplace.net/2018/unification/
;; https://github.com/clojure/core.unify
;; http://mullr.github.io/micrologic/literate.html

(declare unify)
(declare resolve-type)
(declare resolve-type-1)

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
    (and (t/logic? b) (t/bound-t? b subst)) (occurs? a (get subst b) (dissoc subst b))
    (composite? b) (boolean (some (fn [b*]
                                    (occurs? a b* subst)) (seq b)))
    :else false))

(defn dx-dispatch [x y substs]
  (t/type-tag x))

(defmulti dx
  #'dx-dispatch
  :default :default)

(def ^:dynamic *unify-temp-cache* nil)

(defn pending? [x]
  (instance? clojure.lang.IPending x))

(s/fdef pending-unify? :args (s/cat :x any? :y any? :subst ::substs) :ret (s/nilable boolean?))
(defn pending-unify?
  "True if this unify call will cause us to loop"
  [x y substs]
  (let [[_ ret] (find @*unify-temp-cache* [x y substs])]
    (and ret (pending? ret) (not (realized? ret)))))

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

(defn unify-any-any [x y subst]
  (assert x)
  (assert y)
  (or
   (when (t/any-t? x)
     subst)
   (when (isa? @t/types-hierarchy y x)
     subst)
   (when-let [ancestors (and (t/type? y) (t/ancestors y))]
     (->> ancestors
          (some (fn [a]
                  (unify x a subst)))))
   (->> (t/get-equiv-types x)
        (mapcat (fn [xt]
                  (unify xt y subst)))
        (seq))))

(defmethod unify-terms [#'any? #'any?] [x y substs]
  (unify-any-any x y substs))

(defmethod unify-terms [#'any? #'any?] [x y subst]
  (unify-any-any x y subst))

(s/fdef merge-substs :args (s/cat :s ::substs) :ret ::substs)
(defn merge-substs
  [substs]
  ;;; can't merge substs that differ by keys, because e.g. [{?x
  ;;; foo?}{}] will lose the fact that x is possibly unbound.

  (->> substs
       (group-by (fn [s] (-> s keys set)))
       (mapv (fn [[ks ss]]
               (validate! (s/coll-of ::subst) ss)
               (reduce (fn [m1 m2]
                         (reduce (fn [m1 [k2 v2]]
                                   (if (contains? m1 k2)
                                     (update m1 k2 (fn [v1]
                                                     (t/or-t [v1 v2])))
                                     m1)) m1 m2)) ss)))))

(defmethod unify-terms [#'any? nil] [x y subst]
  nil)

(defmethod unify-terms [nil #'any?] [x y subst]
  nil)

(defmethod unify-terms [nil nil] [x y subst]
  nil)

(defn debug-subst [a b]
  (let [a-keys (set (keys a))
        b-keys (set (keys b))]
    (println "debug-subst new keys:" (select-keys b (set/difference b-keys a-keys)))
    (println "debug-subst missing keys:" (select-keys b (set/difference a-keys b-keys)))
    (println "debug-subst changed keys:" (->> a-keys
                                  (filter (fn [ak]
                                            (not= (get a ak) (get b ak))))
                                  (map (fn [ak]
                                         [ak (get a ak) "=>" (get b ak)]))))))

(defn narrow-unify-any-logic-1 [x y subst]
  (let [y* (get subst y)]

    ;;; unifying x and y, but: y is logic, it resolves to a value that
    ;;; is wider than x (such that it doesn't unify), but by narrowing the
    ;;; type more, we can make x and y unify
    (when-let [substs* (and (t/logic? y)
                            (not (t/free-t? y subst))
                            (not (seq (unify x y* [subst])))
                            (not (occurs? y x subst))
                            (unify x y [(dissoc subst y)]))]
      (let [y** (resolve-type y substs*)]
        (when (and (unify y* y** substs*)
                   (not (unify y** y* substs*)))
          ;; (debug-substs y* substs*)
          ;; (debug-substs y** substs*)
          substs*)))))

(s/fdef assoc-subst :args (s/cat :s ::subst :x t/logic? :y any?) :ret ::subst)
(defn assoc-subst [subst x y]
  ;; {:post [(do (println "assoc-subst" x "=>" y) true)]}
  (assert (t/logic? x))
  (assoc subst x y))

(defn unify-any-logic-1 [x y subst]
  (cond
    (get subst y) (let [y* (get subst y)]
                    (or (unify x y* [subst])
                        (when (t/covariant? y)
                          (narrow-unify-any-logic-1 x y subst))))
    (occurs? y x subst) (do (println "occurs?" y x) nil)
    (not (t/ignore? y)) [(assoc-subst subst y x)]
    :else [subst]))

(defn unify-logic-any-1 [x y subst]
  (cond
    (t/bound-t? x subst) (or
                          (unify (get subst x) y [subst])
                          (when (t/contravariant? x)
                            [(update-in subst [x] (fn [xv]
                                                    (t/or-t [xv y])))]))
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
    (and (t/free-t? x subst) (t/free-t? y subst)) [(assoc-subst subst y x)]
    (and (t/free-t? y subst)) [(assoc-subst subst y x)]
    (and (t/free-t? x subst)) [(assoc-subst subst x y)]
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

(defn with-temp-cache [unify-f]
  (fn [x y substs]
    (let [lvars (t/get-lvars [x y (resolve-type x substs) (resolve-type y substs)])
          relevant-keys (set (map (fn [s]
                                    (select-keys s lvars))  substs))
          k [x y relevant-keys]]
      (if-let [[_ ret] (find @*unify-temp-cache* k)]
        (if (and (pending? ret) (not (realized? ret)))
          (do
            (println "with-temp unrealized key:" x y substs)
            nil)
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

(defn with-depth [unify-f]
  (fn [& args]
    (println "unify depth:" (count *unify-seen*))
    (apply unify-f args)))

(defn with-debug [unify-f]
  (fn [& args]
    (let [[x y substs] args
          x-lvars (t/get-lvars x)
          y-lvars (t/get-lvars y)
          lvars (set/union x-lvars y-lvars)]
      (when substs
        (println "unify pre" x y ":" (->> lvars
                                          (map (fn [l]
                                                 (let [r (resolve-type l substs)]
                                                   (if (not= l r)
                                                     [l r]
                                                     [l :free]))))
                                          (into {}))))
      (let [ret (apply unify-f args)]
        (println "unify post" x y "=>" ret)
        ret))))

(defn with-debug-multimethod
  [unify-f]
  (fn [x y substs]
    (println "debug-multimethod" [x y] ":" (debug-multimethod-dispatch unify-terms [x y substs]))
    (unify-f x y substs)))

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
      ;; with-debug-multimethod
      ;; with-debug
      ;; with-depth
      with-doall
      with-no-infinite
      with-unify-call-count
      with-temp-cache
      with-perm-cache
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

(s/fdef valid :args (s/cat :x ::t/type :y ::t/type) :ret boolean?)
(defn valid? [x y]
  (boolean (seq (unify x y))))

(defn first-dispatch [t]
  (unify-term-value t))

(defmulti first-t
  "For regexes, returns a seq of possible values of calling `first` on
  the type"
  #'first-dispatch)

(defmethod first-t :default [x]
  (println "first-t: can't first" x)
  (assert false))

(defmethod first-t 'cat [cat-t]
  (let [[x & xr] (t/cat-types cat-t)]
    (when x
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
        [x]))))

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

(defmethod first-t #'dx? [t]
  nil)

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
  {
   ;; :pre [(do (println "unify dx dx pre" tx ty) true)]
   ;; :post [(do (println "unify dx dx post" tx ty "=>" %) true)]
   }
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
  {:post [;; (do (println "unify dx value" x y "=>" %) true)
          (validate! ::substs %)]}
  (let [val (t/type-value y)]
    (when (seqable? val)
      (unify-dx-dx x (t/cat-t (map t/value-t val)) substs))))

(defmethod unify-terms ['seq-of 'seq-of] [x y substs]
  ;; can't use dxdx here, because both could accept nil, and [seq-of a?] [seq-of b?] shouldn't unify
  (unify (t/type-value x) (t/type-value y) substs))

(defmethod unify-terms ['seq-of #'t/logic?] [x y substs]
  ;; use this to short-circuit
  (if (= (t/type-value x) y)
    substs
    (unify-any-logic x y substs)))

(defmethod unify-terms [#'dx? nil] [x y substs]
  (when (accept-nil? x)
    substs))

(defmethod unify-terms [nil #'dx?] [x y substs]
  (when (accept-nil? y)
    substs))

(defmethod unify-terms [nil nil] [x y substs]
  substs)

(defn unify-tagged-tagged-default
  "Default method for two tagged types. Unify if their (one each) type value unifies"
  [x y substs]
  (when-let [substs (and (t/isa-t? x y) (unify (t/type-value x) (t/type-value y) substs))]
    substs))

(defmethod unify-terms ['coll-of 'coll-of] [x y substs]
  (unify-tagged-tagged-default x y substs))

(defmethod unify-terms ['chunk-buffer 'chunk-buffer] [x y substs]
  (unify-tagged-tagged-default x y substs))

(defmethod unify-terms ['chunk 'chunk] [x y substs]
  (unify-tagged-tagged-default x y substs))

(defmethod unify-terms ['or #'any?] [x y substs]
  ;; {:post [(do (println "unify or any" x y "=>" %) true)]}
  (or
   (when (every? (fn [s] (occurs? y x s)) substs)
     substs)
   (->> (t/or-types x)
        (mapcat (fn [x]
                  (unify x y substs)))
        (filter identity)
        (distinct)
        (doall)
        (seq))
   (when (and (some t/class-t? (t/or-types x))
              (some (fn [yt]
                      (or (t/class-t? yt)
                          (t/instance-or-t? yt))) (t/get-equiv-types y)))
     (->> (t/get-equiv-types y)
          (filter (fn [yt]
                    (or (t/class-t? yt)
                        (t/instance-or-t? yt))))
          (mapcat (fn [yt]
                    (unify x yt substs)))))))

(defn unify-any-or [x y substs]
  (let [rets (->> (t/or-types y)
                  (combo/subsets)
                  (drop 1)
                  (butlast)
                  (map (fn [y*]
                         (unify x (t/or-t y*) substs))))]
    (when (every? seq rets)
      (apply concat rets))))

(defmethod unify-terms [#'any? 'or] [x y substs]
  (unify-any-or x y substs))

(defmethod unify-terms ['or 'or] [x y substs]
  (unify-any-or x y substs))

(defmethod unify-terms [#'any? 'and] [x y substs]
  (->> (t/type-value y)
       (map (fn [y*]
               (unify x y* substs)))
       (filter identity)
       (apply concat)))

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
  (if (unify (t/type-value x) y substs)
    nil
    substs))

(defmethod unify-terms ['not 'not] [x y substs]
  (when-let [substs (unify (t/type-value x) (t/type-value y) substs)]
    substs))

(defmethod unify-terms ['alt #'any?] [alt-x y substs]
  (->> alt-x
       (t/alt-types)
       (mapcat (fn [x]
                 (if (nil? x)
                   substs
                   (unify x y substs))))))

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

(defn get-var-type [v]
  (or (data/get-ann v)
      ;;(parse/get-spec v)
      (data/get-var-spec v)))

(defmethod unify-terms ['spec 'spec] [x y substs]
  (unify-terms (t/type-value x) (t/type-value y) substs))

(defmethod unify-terms ['spec 'value] [x y substs]
  (let [yv (t/type-value y)]
    (when (seqable? yv)
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

(defmethod unify-terms ['class 'class] [x y substs]
  (let [cx (t/type-value x)
        cy (t/type-value y)]
    (cond
      (and (class? cx) (class? cy) (isa? cy cx)) substs
      :else (unify cx cy substs))))

(defmethod unify-terms ['class #'any?] [x y substs]
  (->>
   (t/class-ancestors y)
   (map (fn [yt]
          (unify x yt substs)))
   (filter identity)
   (distinct)
   (apply concat)
   (seq)))

(defmethod unify-terms ['class 'value] [x v substs]
  {:post [(validate! ::substs %)]}
  (let [cls (t/type-value x)
        val (t/type-value v)]
    (or
     (when (t/logic? cls)
       (unify-logic-any cls val substs))
     (when (instance? cls val)
       substs)
     (when (j/castable? cls (class val))
       substs))))

(defmethod unify-terms ['value #'any?] [x y substs]
  (->>
   (t/get-equiv-types y)
   (filter t/value-t?)
   (map (fn [yt]
          (unify x yt substs)))
   (filter identity)
   (distinct)
   (apply concat)
   (seq)))

(defmethod unify-terms ['value 'value] [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(prefer-method unify-terms [#'any? #'t/logic?] [#'any? #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] [#'t/logic? #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['not #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['value #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['and #'any?])
(prefer-method unify-terms [#'any? #'t/logic?] ['class #'any?])
(prefer-method unify-terms [#'any? 'and] ['or #'any?] )
(prefer-method unify-terms [#'any? 'and] ['sequential #'any?])
(prefer-method unify-terms [#'any? 'and] ['value #'any?])
(prefer-method unify-terms [#'any? 'and] ['and #'any?])
(prefer-method unify-terms [#'any? 'and] ['class #'any?])
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
(prefer-method unify-terms [#'dx? #'dx?] ['chunked-seq-of 'chunked-seq-of])
(prefer-method unify-terms ['chunked-seq-of 'chunked-seq-of] ['coll-of 'coll-of])
(prefer-method unify-terms [#'dx? #'dx?] ['coll-of 'coll-of])
(prefer-method unify-terms [#'any? 'or] ['class #'any?])
(prefer-method unify-terms [#'any? 'or] ['value #'any?])

(defn resolve-type-dispatch [t subst]
  (t/type-tag t))

(defmulti resolve-type* #'resolve-type-dispatch)

(defmethod resolve-type* :default [t subst]
  t)

(def ^:dynamic *resolve-seen* #{})

(s/fdef resolve-type-1 :args (s/cat :t any? :s ::subst) :ret any?)
(defn resolve-type-1
  [t subst]
  (if-not (contains? *resolve-seen* t)
    (binding [*resolve-seen* (conj *resolve-seen* t)]
      (let [t* (get subst t t)]
        (cond
          (and (t/logic? t*) (not= t t*)) (resolve-type-1 t* subst)
          :else (or (resolve-type* t* subst) t*))))
    t))

(s/fdef resolve-type :args (s/cat :t any? :s ::substs) :ret any?)
(defn resolve-type [t substs]
  (->> substs
       (map (fn [s]
              (resolve-type-1 t s)))
       (t/or-t)))

(defmethod resolve-type* 'cat [t subst]
  (t/cat-t (map #(resolve-type-1 % subst) (t/cat-types t))))

(defmethod resolve-type* 'fn [t subst]
  (->> (nth t 1)
       (map (fn [[args ret]]
              [(resolve-type-1 args subst) (resolve-type-1 ret subst)]))
       (into {})
       (t/fn-t)))

(defmethod resolve-type* 'or [t subst]
  (->> t
       (t/or-types)
       (map #(resolve-type-1 % subst))
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
       (map #(resolve-type-1 % subst))
       (t/and-t)))

(defmethod resolve-type* 'class [t subst]
  (t/class-t (resolve-type-1 (t/class-value t) subst)))

(defmethod resolve-type* 'maybe [t subst]
  (t/maybe-t (resolve-type-1 (t/maybe-value t) subst)))

(defmethod resolve-type* 'value [t subst]
  (if (t/logic? (t/type-value t))
    (t/value-t (resolve-type-1 (t/type-value t) subst))
    t))

(defmethod resolve-type* 'seq-of [t subst]
  (t/seq-of (resolve-type-1 (t/type-value t) subst)))

(defmethod resolve-type* 'coll-of [t subst]
  (t/coll-of (resolve-type-1 (t/type-value t) subst)))

(defmethod resolve-type* 'invoke [t subst]
  (apply t/invoke-t (map (fn [t] (resolve-type-1 t subst)) (t/type-values t))))

(defn recursive-type? [t subst]
  (let [t-lvars (t/get-lvars t)
        t* (resolve-type t subst)
        t*-lvars (t/get-lvars t*)
        ret (and t*
                 (not= t t*)
                 (->> (set/intersection t-lvars t*-lvars)
                      (remove (fn [t]
                                (t/free-t? t subst)))
                      (seq)
                      (boolean)))]
    ret))

(instrument-ns)
