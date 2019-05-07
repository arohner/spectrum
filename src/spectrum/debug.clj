(ns spectrum.debug
  (:require [clojure.math.combinatorics :as combo]
            [clojure.spec.alpha :as s]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [spectrum.conform :as c]
            [spectrum.debug :as d]
            [spectrum.types :as t]
            [spectrum.util :refer [validate!]]))

(defn shrink-type-dispatch [t path]
  (t/type-tag t))

(defmulti shrink-type-ops #'shrink-type-dispatch)

(defmethod shrink-type-ops :default [t path]
  [])

(defmethod shrink-type-ops 'cat [t path]
  {:post [(validate! (s/coll-of fn?) %)]}
  (assert (t/cat-t? t))
  (let [vals (t/type-values t)]
    (when (pos? (count vals))
      (->> [(->> vals
                 (combo/subsets)
                 (butlast)
                 (map (fn [subset]
                        (with-meta
                          (fn [subst]
                           (println "shrink cat" path t "=>" (vec subset))
                           (assert (get-in subst path))
                            (assoc-in subst path (t/cat-t (vec subset))))
                          {::path path
                           ::op 'cat}))))
            (->> vals
                 (map-indexed (fn [i t]
                                (shrink-type-ops t (conj path (inc i)))))
                 (apply concat))]
           (apply concat)))))

(defmethod shrink-type-ops 'or [t path]
  {:post [(validate! (s/coll-of fn?) %)]}
  (let [vals (vec (t/type-value t))]
    (when (pos? (count vals))
      (->> [(->> vals
                 (combo/subsets)
                 (butlast)
                 (mapcat (fn [subset]
                           (->> subset
                                (combo/permutations)
                                (filter (fn [p]
                                          (boolean (t/or-t (vec p)))))
                                (mapcat (fn [p]
                                          (concat
                                           [(with-meta
                                              (fn [subst]
                                               (println "shrink or" path t "=>" p)
                                               (assert (get-in subst path))
                                                (assoc-in subst path (t/or-t (vec p))))
                                              {::path path
                                               ::op 'or})])))))))
            (->> vals
                 (map-indexed (fn [i t]
                                (shrink-type-ops t (conj path 1 i))))
                 (apply concat))]
           (apply concat)))))

(defmethod shrink-type-ops 'and [t path]
  {:post [(validate! (s/coll-of fn?) %)]}
  (let [vals (vec (t/type-value t))]
    (when (pos? (count vals))
      (->> [(->> vals
                 (combo/subsets)
                 (butlast)
                 (mapcat (fn [subset]
                           (->> subset
                                (combo/permutations)
                                (map (fn [p]
                                       (with-meta (fn shrink-and [subst]
                                                    (println "shrink and" path t "=>" p)
                                                    (assert (get-in subst path))
                                                    (assoc-in subst path (t/and-t (vec p))))
                                         {::path path
                                          ::op 'and})))))))
            (->> vals
                 (map-indexed (fn [i t]
                                (shrink-type-ops t (conj path 1 i))))
                 (apply concat))]
           (apply concat)))))

(defn shrink-substs-key [subst path]
  (let [t (get-in subst path)]
    (shrink-type-ops t path)))

(defn shrink-substs-operations
  "return a seq of fns to try to shrink substs"
  [subst]
  (let [ks (keys subst)]
    (->> [(map (fn [k]
                 (with-meta
                   (fn [s]
                     (dissoc s k))
                   {::path [k]
                    ::op 'key})) ks)
          (mapcat (fn [k]
                    (shrink-substs-key subst [k])) ks)]
         (apply concat))))

(defn clarify-names [subst]
  (let [lvars (set/union (set (keys subst))
                         (set (mapcat t/get-lvars (vals subst))))
        rename-map (->>
                    lvars
                    (map-indexed (fn [i l]
                                   [l (symbol (str "?" (t/logic-name l) i))]))
                    (into {}))]

    (t/rename rename-map subst)))

(defn subst-size [s]
  (let [size (atom 0)]
    (walk/postwalk (fn [f]
                     (swap! size inc)
                     f)
                   s)
    @size))

(defn subst-smaller?
  "Truthy if a < b"
  [a b]
  (< (subst-size a) (subst-size b)))

(defn shrink
  "Given f, a fn of [subst -> bool], shrink subst until arriving at the smallest subst that still returns truthy"
  [f subst]
  (let [ops (shrink-substs-operations subst)]
    (let [op (->> ops
                  (filter (fn [op]
                            (let [subst* (op subst)]
                              (when-not (s/valid? ::c/subst subst*)
                                (println "shrink invalid subst:" (-> f meta) subst*))
                             (validate! ::c/subst subst*)
                             (f subst*))))
                  (first))]
      (if op
        (do
          (println "shrinking!")
          (assert (subst-smaller? (op subst) subst))
          (recur f (op subst)))
        subst))))

(defn with-assert?
  [f]
  (fn [subst]
    (try
      (f subst)
      false
      (catch AssertionError e
        true))))
