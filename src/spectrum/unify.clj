(ns spectrum.unify
  (:require [clojure.core :as c]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.zip :as zip]
            [clojure.walk :as walk]
            [spectrum.util :refer [instrument-ns]]))

;; based on https://eli.thegreenplace.net/2018/unification/
;; https://github.com/clojure/core.unify
;; http://mullr.github.io/micrologic/literate.html

(declare unify)

(defn ignore? [sym] (= '_ sym))

(defn logic? [x]
  (or (and (symbol? x) (= \? (-> x name first)))
      (ignore? x)))

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

(def lvar-counter (atom -1))

(defn next-lvar []
  (swap! lvar-counter inc))

(s/fdef lvar-name :args (s/cat :l logic?) :ret string?)
(defn lvar-name [x]
  (-> x name (subs 1)))

(s/fdef freshen-lvar :args (s/cat :l logic?) :ret logic?)
(defn freshen-lvar
  "Given an lvar, return a new lvar with a unique name"
  [x]
  (as-> x $
    (lvar-name $)
    (str "?" $ (next-lvar))
    (symbol $)))

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
  "Given a form, walk it and replace all lvars with unique versions"
  [form]
  (let [lvars (get-lvars form)
        replace-map (->> lvars
                         (map (fn [l]
                                [l (freshen-lvar l)]))
                         (into {}))]
    (rename replace-map form)))

(defn composite? [x]
  (cond
    (logic? x) false
    (coll? x) true))

(defn wildcard? [form]
  (and (composite? form)
       (= '& (first form))))

(defn occurs?
  "Does v occur anywhere inside typ"
  [v typ subst]
  {:pre [(logic? v)]}
  (cond
    (= v typ) true
    (and (logic? typ) (get subst typ)) (recur v (get subst typ) subst)
    (composite? typ) (some (fn [e] (occurs? v e subst)) (seq typ))
    :else false))

(defn unify-variable [v typ subst]
  {:pre [(logic? v)]}
  (cond
    (get subst v) (unify (get subst v) typ subst)
    (and (logic? typ) (get subst typ)) (unify v (get subst typ) subst)
    (occurs? v typ subst) nil
    :else (do
            (if (not (ignore? v))
              (assoc subst v typ)
              subst))))

(defprotocol IUnifyTerms
  (unify-terms* [u v subst]
    "extensible unification"))

(defn unify-terms [u v subst]
  ;; {:post [(do (when-not %
  ;;               (println "unify-terms" u v "failed")) true)]}
  (unify-terms* u v subst))

(extend-protocol IUnifyTerms
  Object (unify-terms* [u v subst] nil)
  nil    (unify-terms* [u v subst] nil))

(extend-protocol IUnifyTerms
  clojure.lang.Sequential
  (unify-terms* [x y subst]
    (when (and (seqable? y) (seq y))
      (->> subst
           (unify (first x) (first y))
           (unify (rest x) (rest y)))))
  clojure.lang.IPersistentSet
  (unify-terms* [x y subst]
    (when (and (set? y))
      (->> subst
           (unify (first x) (first y))
           (unify (rest x) (rest y)))))
  clojure.lang.IPersistentMap
  (unify-terms* [x y subst]
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
                              (unify (dissoc x x-k) (dissoc y y-k))))))))))

(defn contains
  "Custom unifier goal, unifies if x is a collection, and y is an
  element in the collection"
  [coll]
  (reify IUnifyTerms
    (unify-terms* [x y subst]
      (when (c/contains? (set coll) y)
        subst))))

(defn submap
  "custom unifier. Unify when x is a submap, y is a map, and all keys
  and values present in x unify with their keys in y"
  [m]
  (assert (map? m))
  (reify IUnifyTerms
    (unify-terms* [x y subst]
      (let [[x-k x-v] (->> m (sort-by (fn [[k v]] (logic? k))) first)]
        (cond
          (and (= {} m) (map? y)) subst
          (contains? y x-k) (->> subst
                                 (unify x-v (get y x-k))
                                 (unify (submap (dissoc m x-k)) (dissoc y x-k)))
          (logic? x-k) (->> (keys y)
                            (map (fn [y-k]
                                   (when-let [subst (->> subst
                                                         (unify x-k y-k)
                                                         (unify (get m x-k) (get y y-k)))]
                                     [x-k y-k subst])))
                            (filter identity)
                            (first)
                            ((fn [[x-k y-k subst]]
                               (->> subst
                                    (unify (submap (dissoc m x-k)) (dissoc y y-k)))))))))))

(defmacro with-subst
  "Given"
  [subst-keys & body]
  `(fn [subst#]
     (let [{:keys []}]
       ~@body)))

(s/fdef unify :ret (s/nilable map?))
(defn unify
  "Unifies term x and y with initial subst.

    Returns a subst (map of name->term) that unifies x and y, or nil if
    they can't be unified."
  ([x y]
   (unify x y {}))
  ([x y subst]
   ;; {:post [(do (println "unify" x y subst "=>" %) true)]}
   (cond
     (nil? subst) nil
     (= x y) subst
     (logic? x) (unify-variable x y subst)
     (logic? y) (unify-variable y x subst)
     (wildcard? x) (unify-variable (second x) (seq y) subst)
     (wildcard? y) (unify-variable (second y) (seq x) subst)
     :else (or (unify-terms x y subst)
               (unify-terms y x subst)))))

(instrument-ns)
