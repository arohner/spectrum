(ns spectrum.unify
  (:require [clojure.zip :as zip]
            [clojure.walk :as walk]
            [spectrum.conform :as c]))

;; based on https://eli.thegreenplace.net/2018/unification/

(declare unify)

(defn composite? [x]
  (cond
    (logic? x) false
    (coll? x) true))

(defn logic? [x]
  (or (c/logic? x)
      (and (symbol? x) (= \? (-> x name first)))))

(defn occurs?
  "Does v occur anywhere inside typ"
  [v typ subst]
  {:pre [(logic? v)]}
  (cond
    (= v typ) true
    (and (logic? typ) (get subst typ)) (recur v (get subst typ) subst)
    (c/spect? type) (some (fn [e] (occurs? v e subst)) (c/elements typ))
    (composite? typ) (some (fn [e] (occurs? v e subst)) (seq typ))
    :else false))

(defn unify-variable [v typ subst]
  {:pre [(logic? v)]
   :post [(do (println "unify-variable:" v typ "=>" %) true)]}
  (cond
    (get subst v) (unify (get subst v) typ subst)
    (and (logic? typ) (get subst typ)) (unify v (get subst typ) subst)
    (occurs? v typ subst) nil
    :else (do
            (assoc subst v typ))))

(defn unify
   "Unifies term x and y with initial subst.

    Returns a subst (map of name->term) that unifies x and y, or nil if
    they can't be unified."
  ([x y]
   (unify x y {}))
  ([x y subst]
   {:post [(do (when (not %)
                 (println "unify fail:" x y)) true)]}
   (cond
     (nil? subst) nil
     (= x y) subst
     (c/logic? x) (unify-variable x y subst)
     (c/logic? y) (unify-variable y x subst))))
