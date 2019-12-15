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
            [spectrum.util :refer [instrument-ns validate! defn-memo debug-multimethod-dispatch inspect]])
  (:import [clojure.lang IPersistentCollection IPersistentMap IPersistentSet Sequential]))

;; inspired by:
;; https://eli.thegreenplace.net/2018/unification/
;; https://github.com/clojure/core.unify
;; http://mullr.github.io/micrologic/literate.html

(declare unify)
(declare unify-terms)
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

(defn free-t? [t subst]
  (= t (resolve-type-1 t subst)))

(s/fdef occurs? :args (s/cat :x (s/nilable ::t/type) :y any? :s ::subst) :ret boolean?)
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

(defn cyclic-1? [t subst]
  (and (t/logic? t) (get subst t) (= t (resolve-type-1 t subst))))

(defn cyclic-t? [t substs]
  (and (t/logic? t) (some (fn [s] (and (get s t)
                                       (= t (resolve-type-1 t s)))) substs)))

(defn dx-dispatch [x y substs]
  (t/type-tag x))

(defmulti dx*
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

(ns-unmap 'spectrum.conform 'unify-terms)

(defn dx [x y substs]
  (dx* x y substs))

(defn var-pred? [x]
  (and (var? x)
       (-> x .sym t/predicate-symbol?)))

(s/def ::subst (s/map-of t/logic? any?))
(s/def ::substs (s/nilable (s/coll-of ::subst :kind sequential? :min-count 1)))

(s/fdef assoc-subst :args (s/cat :s ::subst :x t/logic? :y any?) :ret ::subst)
(defn assoc-subst [subst x y]
  ;; {:post [(do (println "assoc-subst" x "=>" y) true)]};
  (assert (t/logic? x))
  (assoc subst x y))

(defn unify-any-logic-1 [x y subst]
  ;; {:post [(do (println "any-logic-1:" x y "=>" (boolean %)) true)]}
  ;; (println "any-logic-1:" x "=" (get subst x) y "=" (get subst y))
  (cond
    (occurs? y x subst) nil
    (and (t/bound-t? y subst) (free-t? y subst)) (unify x y [(dissoc subst y)])
    (find subst y) (unify x (get subst y) [subst])
    (free-t? y subst) [(assoc-subst subst y x)]
    :else (do (assert false (print-str "unify-any-logic:" x y subst)) [subst])))

(s/fdef unify-any-logic :args (s/cat :x any? :y any? :substs ::substs) :ret ::substs)
(defn unify-any-logic [x y substs]
  (some->> substs
           (mapcat (fn [s]
                     (unify-any-logic-1 x y s)))
           (filter identity)
           (seq)))

(defn merge-substs
  [substs]
  (let [ks (apply set/union (map (comp set keys) substs))]
    (some->> substs
             (reduce (fn [final s]
                       (reduce (fn [final k]
                                 (let [v (get s k k)]
                                   (update-in final [k] (fnil conj #{}) v))) final ks)) {})
             (map (fn [[k vs]]
                    [k (t/or-t (vec vs))]))
             (into {})
             (conj []))))

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
                            (t/bound-t? y subst)
                            (not (seq (unify x y* [subst])))
                            (not (occurs? y x subst))
                            (unify x y [(dissoc subst y)]))]
      (let [y** (resolve-type y substs*)]
        (when (unify y* y** substs*)
          ;; (debug-substs y* substs*)
          ;; (debug-substs y** substs*)
          substs*)))))

(defn narrow-unify-1 [x y subst]
  (let [y* (get subst y)]

    ;;; unifying x and y, but: y is logic, it resolves to a value that
    ;;; is wider than x (such that it doesn't unify), but by narrowing the
    ;;; type more, we can make x and y unify
    (when-let [substs* (and (t/logic? y)
                            (t/bound-t? y subst)
                            (not (seq (unify x y* [subst])))
                            (not (occurs? y x subst))
                            (unify x y [(dissoc subst y)]))]
      (let [y** (resolve-type y substs*)]
        ;; (println "narrow-unify:" y "=>" y* "=>" y**);
        (when (unify y* y** substs*)
          ;; (println "narrow-unify:" y "=>" y* "=>" y** "successful")
          ;; (debug-substs y* substs*)
          ;; (debug-substs y** substs*)
          substs*)))))

(defn narrow-unify [x y substs]
  (->> substs
       (mapcat (fn [s]
              (narrow-unify-1 x y s)))
       (filter identity)
       seq))

(defn unify-logic-any-1 [x y subst]
  ;; {:post [(do (println "logic-any-1" x y "=>" (boolean %)) true)]}
  (cond
    (occurs? x y subst) nil
    (and (get subst x) (= x (resolve-type-1 x subst))) [(dissoc subst x)]
    (get subst x) (unify (get subst x) y [subst])
    (nil? (get subst x)) [(assoc subst x y)]
    :else (do (assert false (print-str "unify-logic-any-1:" x y "x*" (resolve-type-1 x subst) "bound x?" (t/bound-t? x subst) "free x?" (free-t? x subst))))))

(defn unify-logic-any [x y substs]
  (some->> substs
           (mapcat (fn [s]
                     (unify-logic-any-1 x y s)))
           (filter identity)
           (seq)))

(defn unify-logic-logic-1 [x y s]
  (let [free? (fn [z]
                (nil? (get s z)))]
    (cond
      (= x y) [s]
      (and (free? x) (free? y)) [(assoc-subst s y x)]
      (free? y) [(assoc-subst s y x)]
      (free? x) [(assoc-subst s x y)]
      :else (or (unify (get s x) (get s y) [s])))))

(defn unify-logic-logic [x y substs]
  (->> substs
       (mapcat (fn [s]
                 (unify-logic-logic-1 x y s)))
       (filter identity)
       (seq)))

(defn unify-sequential-any [x y substs]
  {:post [(do (println "unify sequential any" x y "=>" % ) true)]}
  (when (and (seqable? y) (seq y))
    (some->> substs
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defn unify-set-any [x y subst]
  (when (and (seqable? y) (seq y))
    (some->> subst
             (unify (first x) (first y))
             (unify (rest x) (rest y)))))

(defn unify-map-map [x y subst]
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
        (let [ret (apply unify-f args)]
          ;; (when (> (count @*unify-temp-cache*) 100)
          ;;   (println "temp-cache size:" (count @*unify-temp-cache*)))
          ret))
      (apply unify-f args))))

(defn cacheable? [x y]
  (and (= #{} (t/get-lvars x))
       (= #{} (t/get-lvars y))))

;;; two cache levels. One of just [x y], which is persistent across
;;; calls to unify, only used when no logic vars present. second
;;; level, [x y substs] only present in the stack of a single
;;; top-level unify call

(defn with-substs-limit [unify-f]
  (fn [x y substs]
    (println "count substs in" x y ":" (count substs) "in")
    (when (> (count substs) 1000)
      (assert false (print-str "too many substs in:" x  y ":" (count substs) "in")))
    (when-let [ret (unify-f x y substs)]
      (println "count substs out:" x y ":" (count substs) "in" (count ret) "out")
      (when (> (count ret) 1000)
        (assert false (print-str "too many substs out:" x y ":" (count substs) "in" (count ret) "out")))
      ret)))

(def perm-cache (atom {}))

(defn with-perm-cache [unify-f]
  (fn [x y substs]
    (if-let [[k ret] (find @perm-cache [x y])]
      (if ret
        (-> substs (with-meta {::cache-hit 1 ::cache-total 1}))
        nil)
      (let [ret (unify-f x y substs)]
        (when (cacheable? x y)
          (swap! perm-cache assoc [x y] (boolean ret)))
        (when ret
          (-> ret (with-meta {::cache-hit 0 ::cache-total 1})))))))

(s/fdef get-relevant-keys :args (s/cat :t any? :s ::subst :seen (s/? (s/coll-of t/logic? :kind set?))) :ret (s/coll-of t/logic? :kind set?))
(defn get-relevant-keys
  "return all logic variables that will be checked while resolving t"
  ([t subst]
   (get-relevant-keys t subst #{}))
  ([t subst seen]
   (let [lvars (t/get-lvars t)]
     (set/union lvars (set (mapcat (fn [l] (some-> (get subst l)
                                                   (get-relevant-keys subst (set/union seen lvars)))) (set/difference lvars seen)))))))

(defn get-relevant-substs [t substs]
  (->> substs
       (map (fn [s]
              (select-keys s (get-relevant-keys t s))))
       (filter identity)
       distinct
       vec))

(defn with-temp-cache [unify-f]
  (fn [x y substs]
    {:post [;; (do (println "with-temp-cache" x y "=>" (boolean %)) true)
            ;; (validate! ::substs %)
            ]}
    (->> substs
         (map (fn [s]
                (let [relevant-keys (get-relevant-keys [x y] s)
                      k [x y (select-keys s relevant-keys)]]
                  (assert *unify-temp-cache*)
                  (if-let [[_ cached] (find @*unify-temp-cache* k)]
                    (if (and (pending? cached) (not (realized? cached)))
                      (do
                        ;; (println "with-temp pending" k)
                        ;; (assert false)
                        nil)
                      (if cached
                        (->> cached
                             (mapv (fn [c]
                                     (merge s c)))
                             (#(with-meta % {::cache-hit 1
                                             ::cache-total 1})))
                        nil))
                    (let [_ (swap! *unify-temp-cache* assoc k (promise))
                          ret (unify-f x y [s])
                          ret (when ret
                                (with-meta ret {::cache-hit 0
                                                ::cache-total 1}))]
                      (let [cached (get @*unify-temp-cache* k)
                            new-val (when ret
                                      (mapv (fn [r] (select-keys r relevant-keys)) ret))]
                        (assert (or (and ret new-val) (and (not ret) (not new-val))))
                        (assert (and (pending? cached) (not (realized? cached))))
                        (swap! *unify-temp-cache* (fn [m] (assoc m k new-val))))
                      ret)))))
         ((fn [substss]
            (let [metas (->> substss (map meta) (filter identity))
                  cache-hit (apply + (map ::cache-hit metas))
                  cache-total (apply + (map ::cache-total metas))]
              (some->> substss
                       (apply concat)
                       (seq)
                       (doall)
                       (#(with-meta % {::cache-hit cache-hit
                                       ::cache-total cache-total})))))))))

(def ^:dynamic *cache-hit-stats* nil)

(defn with-cache-hit-stats [unify-f]
  (fn [x y substs]
    (if *cache-hit-stats*
      (let [ret (unify-f x y substs)
            cache (-> ret meta)]
        (swap! *cache-hit-stats* (fn [c] (merge-with + c cache)))
        ret)
      (binding [*cache-hit-stats* (atom {})]
        (let [ret (unify-f x y substs)
              cache @*cache-hit-stats*]
          ;; (when (::cache-total cache)
          ;;   (println "unify" x y "cache-hit-stats:" (format "%d/%d=%.2f%%" (::cache-hit cache) (::cache-total cache) (* 100 (/ (::cache-hit cache) (double (::cache-total cache)))))))
          ret)))))

(defn with-merge-substs [unify-f]
  (fn [x y substs]
    (let [ret (unify-f x y substs)]
      (when ret
        (merge-substs ret)))))

(defn with-distinct-substs [unify-f]
  (fn [x y substs]
    (let [ret (unify-f x y substs)]
      (when ret
        (distinct ret)))))

(def ^:dynamic *unify-seen* nil)

(defn with-detect-loop [unify-f]
  (fn [x y substs]
    (let [f (fn []
              (let [k [x y substs]
                    seen? (some #(= k %) @*unify-seen*)
                    _ (swap! *unify-seen* conj [x y substs])
                    ret (unify-f x y substs)
                    expanding? (> (count ret) (count substs))]
                ;; (when (and seen? (= [x y] '[[or [[seq-of ?x+269] [seq-of ?y+268]]] [or [?x+269 [seq-of ?y296] [seq-of ?x+269]]]]))
                ;;   (println "seen?" [x y] seen?)
                ;;   (assert false))
                ;; (when (and seen? (> (count ret) (count substs)))
                ;;   (println "loop!" x y substs "=>" ret (take 2 (clojure.data/diff substs ret)))
                ;;   (assert false))
                ret))]
      (if (nil? *unify-seen*)
        (binding [*unify-seen* (atom [])]
          (f))
        (f)))))

(def ^:dynamic *unify-call-count* nil)

(defn with-call-count [unify-f]
  (fn [x y substs]
    (if *unify-call-count*
      (do
        (swap! *unify-call-count* inc)
        (let [starting @*unify-call-count*
              ret (unify-f x y substs)
              ending @*unify-call-count*
              call-count (- ending starting)]
          (when (> call-count 10)
            (println "with-call-count:" x y call-count))
          ret))
      (let [counter (atom 1)]
        (binding [*unify-call-count* counter]
          (let [ret (unify-f x y substs)]
            (println "with-call-count:" @counter)
            ret))))))

(defn with-no-infinite [unify-f]
  (fn [x y substs]
    (when (> @*unify-call-count* 3000)
      (assert false))
    (unify-f x y substs)))

(defn with-larger-substs [unify-f]
  (fn [x y substs]
    (let [ret (unify-f x y substs)]
      (when ret
        (assert (every? (fn [r]
                          (some (fn [s]
                                  (>= (count r) (count s))) substs)) ret)))
      ret)))

(def ^:dynamic *unify-depth* nil)

(defn with-depth [unify-f]
  (fn [x y substs]
    (binding [*unify-depth* (inc (or *unify-depth* 0))]
      (when (= 0 (mod *unify-depth* 100))
        (println "with-depth:" (count *unify-depth*)))
      (unify-f x y substs))))

(defn with-timing [unify-f]
  (fn [x y substs]
    (let [start (System/nanoTime)
          ret (unify-f x y substs)
          stop (System/nanoTime)
          elapsed-ms (/ (- stop start) 1000000.0)]
      (assert (< elapsed-ms 2000) (print-str "timing:" x y "elapsed:" elapsed-ms "call-count:" @*unify-call-count* "depth:" *unify-depth*))
      ret)))

(defn debug-substs
  "Given a subst, print the parts relevant to type t"
  [t substs]
  (println "debug-relevant" t "relevant subst:" (->> substs
                                                     (map (fn [s]
                                                            (select-keys s (get-relevant-keys t s))))
                                                     (filter identity)
                                                     (distinct))))
(defn with-debug [unify-f]
  (fn [& args]
    (let [[x y substs] args
          x-lvars (t/get-lvars x)
          y-lvars (t/get-lvars y)
          lvars (set/union x-lvars y-lvars)]
      (println "unify pre" x y ":" (get-relevant-substs [x y] substs))
      (let [ret (apply unify-f args)]
        (println "unify post" x y "=>" (boolean ret))
        ret))))

(defn with-require-substs
  "It's easy to accidentally call the 2-arity unify from inside
  unify-terms, which can cause serious, hard-to-find bugs. Assert that
  never happens"
  [unify-f]
  (fn
    ([x y]
     (unify-f x y [{}]))
    ([x y substs]
     (unify-f x y substs))))

(defn with-doall [unify-f]
  (fn [& args]
    (->> (apply unify-f args)
         (seq))))

(defn unify-any-any [x y substs]
  (or
   (when (isa? @t/types-hierarchy y x)
     substs)
   (when (= #'any? x)
     substs)
   (let [x-ancestors (when (t/type? x) (-> x t/ancestors (conj x)))
         y-ancestors (when (t/type? y) (t/ancestors y))]
     (some->>
      (disj y-ancestors #'any?)
      (filter (fn [ya]
                (contains? x-ancestors ya)))
      (some (fn [ya]
              (unify x ya substs))))
     (->> (t/get-equiv-types x)
          (mapcat (fn [xt]
                    (unify xt y substs)))
          (seq)))))

(defn unify-or-any [x y substs]
  ;; {:pre [(do (println "unify or any pre" x y) true)]
  ;;  :post [(do (println "unify or any" x y "=>" %) true)]}
  (or
   (when (every? (fn [s] (occurs? y x s)) substs)
     substs)
   (->> x
        t/type-value
        (mapcat (fn [xt]
                  (unify xt y substs)))
        (filter identity)
        (distinct)
        (doall)
        (seq))
   (when (and (some t/class-t? (t/type-value x))
              (some (fn [yt]
                      (or (t/class-t? yt)
                          (t/instance-or-t? yt))) (t/get-equiv-types y)))
     (->> (t/get-equiv-types y)
          (filter (fn [yt]
                    (or (t/class-t? yt)
                        (t/instance-or-t? yt))))
          (mapcat (fn [yt]
                    (unify x yt substs)))))
   (when (t/logic? y)
     (unify-any-logic x y substs))))

(defn unify-or-or [x y substs]
  (let [ys (-> y t/type-value set)]
    (reduce (fn [substs x*]
              (when substs
                (or
                 (when (contains? ys x*)
                   substs)
                 (->> ys
                      (some (fn [y*]
                              (unify x* y* substs))))))) substs (t/type-value x))))

(defn unify-any-or [x y substs]
  ;;; unifies when every item in y unifies individually, or every pair of items, or triple, etc.
  (let [yss (->> y
                 t/type-value
                 (combo/subsets)
                 (drop 1)
                 (butlast)
                 (group-by count))]
    (->> yss
         (map (fn [[cnt ys]]
                (let [rets (->> ys
                                (map (fn [y*]
                                       (unify x (t/or-t y*) substs)))
                                (doall))]
                  ;; (println "cnt" cnt "ys" ys "rets:" rets)
                  (when (every? seq rets)
                    (apply concat rets)))))
         (filter identity)
         (first))))

(defn unify-any-and [x y substs]
  ;; {:post [(do (println "any and" x y "=>" %) true)]}
  (->> (t/type-value y)
       (map (fn [y*]
               (unify x y* substs)))
       (filter identity)
       (apply concat)
       (seq)))

(defn unify-and-any [x y substs]
  (reduce (fn [substs x*]
            (when substs
              (unify x* y substs))) substs (t/type-value x)))

(defn unify-and-and [x y substs]
  (let [ys (-> y t/type-value set)]
    (reduce (fn [substs x*]
              (when substs
                (or
                 (when (contains? ys x*)
                   substs)
                 (->> ys
                      (some (fn [y*]
                              (unify x* y* substs))))))) substs (t/type-value x))))

(defn unify-not-any [x y substs]
  (if (unify (t/type-value x) y substs)
    nil
    substs))

(defn unify-not-not [x y substs]
  (when-let [substs (unify (t/type-value x) (t/type-value y) substs)]
    substs))

(defn unify-spec-spec [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(defn unify-spec-value [x y substs]
  (let [yv (t/type-value y)]
    (when (seqable? yv)
      (unify (t/type-value x) (t/cat-t (map t/value-t yv)) substs))))

(defn unify-any-spec [x y substs]
  (when (not (t/regex? x))
    (unify x (t/type-value y) substs)))

(defn unify-value-value [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(defn unify-value-any [x y substs]
  (->>
   (t/get-equiv-types y)
   (filter t/value-t?)
   (map (fn [yt]
          (unify x yt substs)))
   (filter identity)
   (distinct)
   (apply concat)
   (seq)))

(defn unify-class-class [x y substs]
  (let [cx (t/type-value x)
        cy (t/type-value y)]
    (cond
      (and (class? cx) (class? cy) (or (isa? cy cx) (j/castable? cy cx))) substs
      :else (unify cx cy substs))))

(defn unify-class-any [x y substs]
  (->>
   (t/class-ancestors y)
   (mapcat (fn [yt]
          (unify x yt substs)))
   (filter identity)
   (distinct)
   (seq)))

(defn unify-class-value [x v substs]
  ;; {:post [(validate! ::substs %)]}
  (let [cls (t/type-value x)
        val (t/type-value v)]
    (when-not (class? cls)
      (println "unify-terms:" x v))
    (assert (class? cls))
    (or
     (when (t/logic? cls)
       (unify-logic-any cls val substs))
     (when (instance? cls val)
       substs)
     (when (and (class val) (j/castable? cls (class val)))
       substs))))

(defn unify-fn-fn [x y substs]
  (->> x
       (t/type-value)
       (mapcat (fn [[x-args x-ret]]
                 (->> y
                      (t/type-value)
                      (mapcat (fn [[y-args y-ret]]
                                (some->> substs
                                         (unify x-ret y-ret)
                                         seq
                                         (unify x-args y-args)
                                         seq))))))
       seq))

(defn unify-any-value [x y substs]
  ;; {:post [(validate! ::substs %)]}
  (let [val (t/type-value y)
        spread (when (and (seqable? val) (seq val))
                 (t/spec-t (t/cat-t (map t/value-t val))))]
    (->> [(when (and (contains? @t/value-pred-whitelist x) (x val))
            substs)
          (when spread
            (unify x spread substs))]
         (apply concat)
         seq)))

(defn unify-seqof-seqof [x y substs]
  ;; can't use dxdx here, because both could accept nil, and [seq-of a?] [seq-of b?] shouldn't unify
  (unify (t/type-value x) (t/type-value y) substs))

(defn unify-seqableof-seqof [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(defn unify-seqableof-seqableof [x y substs]
  (unify (t/type-value x) (t/type-value y) substs))

(defn unify-seqof-logic [x y substs]
  ;; use this to short-circuit
  (if (= (t/type-value x) y)
    substs
    (unify-any-logic x y substs)))

(defn unify-tagged-tagged-default
  "Default method for two tagged types. Unify if their (one each) type value unifies"
  [x y substs]
  (when-let [substs (and (t/isa-t? x y) (unify (t/type-value x) (t/type-value y) substs))]
    substs))

(defn unify-term-value [x]
  (cond
    (t/logic? x) #'t/logic?
    (t/value-t? x) #'t/value-t?
    (t/tagged? x) (if (t/parents x)
                    (t/type-tag x)
                    #'any?)
    (var? x) (if (t/parents x)
               x
               #'any?)
    (nil? x) nil
    (sequential? x) ::sequential-literal
    (set? x) ::set-literal
    (map? x) ::map-literal
    :else #'any?))

(defn first-dispatch [t]
  (unify-term-value t))

(defmulti accept-nil?
  "True if this (regex) type may accept no input"
  #'t/type-tag
  :default nil)

(defmethod accept-nil? nil [_]
  false)

(defmethod accept-nil? #'t/alt-t? [t]
  (some nil? (t/alt-types t)))

(defmethod accept-nil? #'t/seq-of? [t]
  true)

(defmethod accept-nil? #'t/cat-t? [t]
  (every? accept-nil? (t/cat-types t)))

(defmethod accept-nil? #'t/value-t? [t]
  (let [val (-> t t/type-value)]
    (if (seqable? val)
      (and (nil? (seq val)) (not= nil val))
      false)))

(defmulti first-t
  "For regexes, returns a seq of possible values of calling `first` on
  the type"
  #'first-dispatch)

(defmethod first-t :default [x]
  (println "first-t: can't first" x)
  (assert false))

(defmethod first-t #'t/cat-t? [cat-t]
  (let [[x & xr] (t/cat-types cat-t)]
    (when x
      (if (t/regex? x)
        (->>
         (concat (first-t x) (when (and (accept-nil? x) xr)
                               (first-t (t/cat-t xr))))
         (filter identity)
         ((fn [ts]
            (if (accept-nil? cat-t)
              (conj ts nil)
              ts)))
         (distinct))
        [x]))))

(defmethod first-t #'t/seq-of? [t]
  (-> t
      (t/seq-value)
      ((fn [x]
         (if (t/regex? x)
           (first-t x)
           [x nil])))))

(defmethod first-t #'t/alt-t? [alt-t]
  (->> alt-t
       t/alt-types
       (mapcat (fn [t]
                 (if (t/regex? t)
                   (first-t t)
                   [t])))))

(defmethod first-t #'t/value-t? [val-t]
  ;; {:post [(validate! (s/nilable (s/coll-of t/value-t?)) %)]}
  (let [val (t/type-value val-t)]
    (when (and (seqable? val) (seq val))
      [(t/value-t (first val))])))

(defn unify-dx-dx [tx ty substs]
  {
   ;; :pre [(do (println "unify dx dx pre" tx ty substs) true)]
   ;; :post [(do (println "unify dx dx post" tx ty "=>" %) true]
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

(defn unify-dx-value [x y substs]
  ;; {:post [(validate! ::substs %)]}
  (let [val (t/type-value y)]
    (when (seqable? val)
      (unify-dx-dx x (t/cat-t (map t/value-t val)) substs))))

(defn dx-vals
  "Given a regex, dx it repeatedly, returning all distinct values"
  [re substs]
  (let [vals (first-t re)
        res (distinct (mapcat (fn [v] (dx re v substs)) vals))]
    (concat
     vals
     (mapcat (fn [{re* :state
                   substs* :substs}]
               (when (and re* (not= re re*))
                 (dx-vals re* substs*))) res))))

(defn unify-collof-spec [x y substs]
  {:post [(validate! ::substs %)]}
  (let [x* (t/type-value x)
        y* (t/type-value y)]
    (when (t/regex? y*)
      (reduce (fn [substs dy]
                (when substs
                  (if dy
                    (unify x* dy substs)
                    substs))) substs (dx-vals y* substs)))))

(s/def :dx/state (s/nilable ::t/type))
(s/def ::dx-ret (s/keys :req-un [:dx/state ::substs]))

(s/def ::dx-rets (s/nilable (s/coll-of ::dx-ret)))

(defn with-dx-substs-limit [dx-f]
  (fn [x y substs]
    (let [ret (dx-f x y substs)]
      (every? (fn [r]
                   (let [{substs-out :substs} r]
                    (when (> (count substs-out) 1000)
                       (assert false (print-str "dx too many substs:" x y (count substs) "in," (count substs-out) "out"))))
                   true) ret)
      ret)))

(defn with-dx-validate [dx-f]
  (fn [x y substs]
    (let [ret (dx-f x y substs)]
      (validate! ::dx-rets ret)
      ret)))

(def dx
  (-> dx*
      ;; with-dx-validate
      with-dx-substs-limit))

(defmethod dx* :default [x y substs]
  ;; {:post [(validate! ::dx-rets %)]}
  (when-let [substs* (unify x y substs)]
    [{:state nil :substs substs*}]))

(defmethod dx* #'t/cat-t? [cat-x y substs]
  ;; {:post [(validate! ::dx-rets %)]}
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
          (when (and (accept-nil? x) xr)
            (dx (t/cat-t xr) y substs))]
         (apply concat)
         (filter identity)
         (seq))))

(defmethod dx* #'t/seq-of? [seq-x y substs]
  (let [x (t/seq-value seq-x)
        substs-orig substs]
    (cond
      (nil? y) [{:state nil :substs substs}]
      (= y x) [{:state nil :substs substs}
               {:state seq-x :substs substs}]
      (t/logic? y) (when-let [substs (unify seq-x y substs)]
                     [{:state nil :substs substs}
                      {:state seq-x :substs substs}])
      :else (when-let [substs (unify x y substs)]
              [{:state nil :substs substs}
               {:state seq-x :substs substs}]))))

(defmethod dx* #'t/alt-t? [alt-x y substs]
  (->> (t/alt-types alt-x)
       (mapcat (fn [at]
                 (dx at y substs)))))

(defmethod dx* #'t/value-t? [val-x y substs]

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

(defn unify-truthy [x y substs]
  substs)

(defn unify-falsey [x y substs]
  nil)

(defn match*
  [x y]
  (fn
    ([xyf f]
     (if (vector? xyf)
       (let [[xf yf] xyf]
         (cond
           (and xf yf (xf x) (yf y)) f
           (and xf (nil? yf) (xf x)) f
           (and yf (nil? xf) (yf y)) f
           (and (nil? xf) (nil? yf)) f
           :else nil))
       (when (xyf x y)
         f)))))

(defn tagged-default? [x]
  (and (t/tagged? x)
       (not (t/regex? x))
       (not (t/or-t? x))
       (not (t/and-t? x))))

(s/fdef unify-terms :ret (s/nilable ::substs))
(defn unify-terms [x y substs]
  (let [match (match* x y)
        i (fn [x] (fn [y] (t/instance-t? x y)))
        _ nil
        matching-unify-f
        (filter
         identity
         [(match [nil? nil?] unify-truthy)
          (match (fn [x y]
                   (and (t/regex? x) (t/regex? y)
                        (not (and (t/seq-of? x) (t/seq-of? y))))) unify-dx-dx)
          (match [nil? accept-nil?] unify-truthy)
          (match [accept-nil? nil?] unify-truthy)
          (match [_ nil?] unify-falsey)
          (match [t/or-t? t/or-t?] unify-any-or)
          (match [t/or-t? _] unify-or-any)
          (match [_ t/or-t?] unify-any-or)
          ;; (match [t/and-t? t/and-t?] unify-and-and)
          (match [t/and-t? _] unify-and-any)
          (match [_ t/and-t?] unify-any-and)
          (match [t/not-t? t/not-t?] unify-not-not)
          (match [t/spec-t? t/spec-t?] unify-spec-spec)
          (match [t/spec-t? t/value-t?] unify-spec-value)
          (match [_ t/spec-t?] unify-any-spec)
          (match [t/not-t? _] unify-not-any)
          (match [t/value-t? t/value-t?] unify-value-value)
          (match [t/class-t? t/value-t?] unify-class-value)
          (match [t/value-t? _] unify-value-any)
          (match [_ t/value-t?] unify-any-value)
          (match [t/fn-t? t/fn-t?] unify-fn-fn)
          (match [t/class-t? t/class-t?] unify-class-class)
          (match [t/class-t? _] unify-class-any)
          (match [t/logic? t/logic?] unify-logic-logic)
          (match [t/logic? _] unify-logic-any)
          (match [_ t/logic?] unify-any-logic)
          (match [t/regex? t/value-t?] unify-dx-value)
          (match [t/seq-of? t/logic?] unify-seqof-logic)
          ;; (match [t/seq-of? t/seq-of?] unify-seqof-seqof)
          (match [t/seqable-of? t/seqable-of?] unify-tagged-tagged-default)
          (match [t/seq-of? t/seq-of?] unify-tagged-tagged-default)
          (match [tagged-default? tagged-default?] unify-tagged-tagged-default)
          (match [(i #'t/coll-of?) t/spec-t?] unify-collof-spec)
          (match [_ _] unify-any-any)])]
    ;; (println "matching:" x y matching-unify-f)
    (->>
     matching-unify-f
     (some (fn [f]
             ;; {:post [(do (when % (println "unify:" x y f "=>" %)) true)]}
             (f x y substs)))
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
      ;; with-larger-substs
      ;; with-no-infinite
      with-temp-cache
      with-cache-hit-stats
      with-perm-cache
      with-ensure-temp-cache
      ;; with-detect-loop
      ;; with-merge-substs
      with-distinct-substs
      ;; with-substs-limit
      ;; with-timing
      ;; with-call-count
      ;; with-depth
      with-require-substs))

(defn debug-unify
  ([x y])
  ([x y substs]
   (let [ret (unify x y substs)]
     (println "debug-unify" x y "=>" (boolean (seq ret)))
     (debug-substs x substs)
     (debug-substs y substs)
     ret)))

(s/fdef valid :args (s/cat :x ::t/type :y ::t/type) :ret boolean?)
(defn valid? [x y]
  (boolean (seq (unify x y))))

(defn value-coll-type
  "Given a 'value holding a persistent collection, return a type that unifies with all elements of the value"
  [v]
  (assert (seqable? (t/type-value v)))
  (->> v
       t/type-value
       (map t/value-t)
       (t/or-t)))

(defn get-var-type [v]
  (or (data/get-ann v)
      ;;(parse/get-spec v)
      (data/get-var-spec v)))

(t/derive-type #'any? #'t/logic?)

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

(defn re-will-accept-dispatch [x]
  {:pre [(t/type-tag x)]
   ;; :post [(do (println "re-will-accept dispatch" x "=>"%) true)]
   }
  (t/type-tag x))

(defmulti re-will-accept
  "Returns a set of types this regex could accept. Do not include nil"
  #'re-will-accept-dispatch)

(defn re-accept-dispatch [x y]
  (t/type-tag x))

(defmethod re-will-accept #'t/seq-of? [seq-x]
  #{(t/type-value seq-x)})

(defmethod re-will-accept #'t/alt-t? [alt-x]
  #{(t/type-value alt-x)})

(defmethod re-will-accept #'t/cat-t? [cat-x]
  (let [[x & xr :as xs] (t/cat-types cat-x)]
    (if (accept-nil? x)
      (if (seq xr)
        (conj x (re-will-accept (t/cat-t xr)))
        #{x})
      #{x})))

(defmulti re-accept
  "Without unifying, assume x accepts y and return a set of possible
  updated regexes. Return the empty set to indicate it will not accept
  anything else. Include nil in the set to indicate it could accept
  nil"
  #'re-accept-dispatch)

(defmethod re-accept #'t/seq-of? [x y]
  #{x nil})

(defmethod re-accept #'t/alt-t? [x y]
  #{})

(defmethod re-accept #'t/cat-t? [x y]
  (let [[xv & xr :as xs] (t/cat-types x)]
    (if (seq xr)
      (if (accept-nil? xv)
        (conj (t/cat-t xr) (re-accept (t/cat-t xr) y))
        #{(t/cat-t xr)})
      #{})))

(defmethod re-accept nil [x y]
  (t/invalid))

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
          :else (or (resolve-type* t* subst) t* t))))
    t))

(s/fdef resolve-type :args (s/cat :t any? :s ::substs) :ret any?)
(defn resolve-type [t substs]
  (->> substs
       (map (fn [s]
              (resolve-type-1 t s)))
       (t/or-t)))

(defmethod resolve-type* #'t/cat-t? [t subst]
  (t/cat-t (map #(resolve-type-1 % subst) (t/cat-types t))))

(defmethod resolve-type* #'t/fn-t? [t subst]
  (->> (nth t 1)
       (map (fn [[args ret]]
              [(resolve-type-1 args subst) (resolve-type-1 ret subst)]))
       (into {})
       (t/fn-t)))

(defmethod resolve-type* #'t/or-t? [t subst]
  (->> t
       (t/type-value)
       (map #(resolve-type-1 % subst))
       (filter identity)
       (t/or-t)
       ((fn [t]
          (if (t/or-t? t)
            (if (every? t/fn-t? (t/type-value t))
              (t/merge-fns (t/type-values t))
              t)
            t)))))

(defmethod resolve-type* #'t/and-t? [t subst]
  (->> t
       (t/and-types)
       (map #(resolve-type-1 % subst))
       (t/and-t)))

(defmethod resolve-type* #'t/class-t? [t subst]
  (t/class-t (resolve-type-1 (t/class-value t) subst)))

(defmethod resolve-type* #'t/maybe-t? [t subst]
  (t/maybe-t (resolve-type-1 (t/maybe-value t) subst)))

(defmethod resolve-type* #'t/value-t? [t subst]
  (if (t/logic? (t/type-value t))
    (t/value-t (resolve-type-1 (t/type-value t) subst))
    t))

(defmethod resolve-type* #'t/seq-of? [t subst]
  (t/seq-of (resolve-type-1 (t/type-value t) subst)))

(defmethod resolve-type* #'t/coll-of? [t subst]
  (t/coll-of (resolve-type-1 (t/type-value t) subst)))

(defmethod resolve-type* #'t/invoke-t? [t subst]
  (apply t/invoke-t (map (fn [t] (resolve-type-1 t subst)) (t/type-values t))))

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
