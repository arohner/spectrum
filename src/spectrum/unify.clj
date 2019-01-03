(ns spectrum.unify
  (:require [clojure.core :as c]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.zip :as zip]
            [clojure.walk :as walk]
            [spectrum.type :as t]
            [spectrum.util :refer [instrument-ns]])
  (:import [clojure.lang IPersistentMap IPersistentSet Sequential]))

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

(defn occurs?
  "Does v occur anywhere inside typ"
  [v typ subst]
  {:pre [(logic? v)]}
  (cond
    (= v typ) true
    (and (logic? typ) (get subst typ)) (recur v (get subst typ) subst)
    (composite? typ) (some (fn [e] (occurs? v e subst)) (seq typ))
    :else false))

(defn unify-term-value [x]
  (cond
    (t/logic? x) ::logic
    (t/tagged? x) (t/type-tag x)
    (var? x) x
    :else (class x)))

(defn unify-terms-dispatch [u v subst]
  [(unify-term-value u) (unify-term-value v)])

(defmulti unify-terms "" #'unify-terms-dispatch)

(defmethod unify-terms [Object Object] [x y subst]
  {:post [(do (println "unify any? any?" x y "=>" %) true)]}
  nil)

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

(defmethod unify-terms [::logic Object] [x y subst]
  (unify-variable x y subst))

(defmethod unify-terms [Object ::logic] [x y subst]
  (unify-variable y x subst))

(defmethod unify-terms [::logic ::logic] [x y subst]
  (unify-variable x y subst))

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
     :else (unify-terms x y subst)
     ;; (logic? x) (unify-variable x y subst)
     ;; (logic? y) (unify-variable y x subst)
     ;; (wildcard? x) (unify-variable (second x) (seq y) subst)
     ;; (wildcard? y) (unify-variable (second y) (seq x) subst)
     ;; :else (or (unify-terms x y subst)
     ;;           (unify-terms y x subst))
     )))

(instrument-ns)
