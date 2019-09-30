(ns spectrum.equations
  (:require [clojure.spec.alpha :as s]
            [spectrum.types :as t]
            [spectrum.util :refer [instrument-ns]]))

(s/def ::eq (s/tuple #{:eq} ::t/fresh-type ::t/fresh-type))
(s/def ::<= (s/tuple #{:<=} ::t/fresh-type ::t/fresh-type))
(s/def ::>= (s/tuple #{:>=} ::t/fresh-type ::t/fresh-type))
(s/def ::true (s/tuple #{:true}))
(s/def ::false (s/tuple #{:false}))

(s/def ::equation (s/or :e ::eq :< ::<= :> ::>= :t ::true :f ::false :a ::ande :o ::ore :i ::imp))
(s/def ::ande (s/cat :a #{:ande} :e (s/coll-of ::equation)))
(s/def ::ore (s/cat :o #{:ore} :e (s/coll-of ::equation)))
(s/def ::imp (s/cat :i #{:imp} :p ::equation :q ::equation))

(s/fdef eq :args (s/cat :x ::t/type :y ::t/type) :ret ::eq)
(defn eq [x y]
  "constraint that (= x y) should be true. invariant"
  [:eq x y])

(s/fdef <= :args (s/cat :x ::t/type :y ::t/type) :ret ::equation)
(defn <=
  "constraint that (valid? x y) should be true. Will narrow y if it is a logic variable, and necessary to satisfy the constraint. covariant"
  [x y]
  [:<= x y])

(s/fdef >= :args (s/cat :x ::t/type :y ::t/type) :ret ::equation)
(defn >=
  "constraint that (valid? x y) should be true. Will widen x if it is a logic variable, and necessary to satisfy the constraint. contravariant"
  [x y]
  [:>= x y])

(s/fdef false-e :args (s/cat :err (s/? string?)) :ret ::equation)
(defn false-e
  ([]
   [:false])
  ([msg]
   [:false msg]))

(s/fdef true-e :args (s/cat) :ret ::equation)
(defn true-e []
  [:true])

(defn true-e? [x]
  (and (vector? x) (= :true (nth x 0))))

(defn and-e? [x]
  (and (vector? x) (= :ande (nth x 0))))

(defn or-e? [x]
  (and (vector? x) (= :ande (nth x 0))))

(defn false-e? [x]
  (and (vector? x) (= :false (nth x 0))))

(s/fdef or-e :args (s/cat :eqs (s/coll-of ::equation)) :ret ::equation)
(defn or-e [eqs]
  (let [eqs (->> eqs
                 (mapcat (fn [e]
                           (if (or-e? e)
                             (nth e 1)
                             [e])))
                 (remove true-e?)
                 (distinct))
        eqs (if (some true-e? eqs)
              [(true-e)]
              (vec eqs))]
    (cond
      (> (count eqs) 1) [:ore (vec eqs)]
      (= (count eqs) 1) (first eqs)
      :else (true-e))))

(s/fdef and-e :args (s/cat :eqs (s/coll-of ::equation)) :ret ::equation)
(defn and-e [eqs]
  (let [eqs (->> eqs
                 (mapcat (fn [e]
                           (if (and-e? e)
                             (nth e 1)
                             [e])))
                 (remove true-e?)
                 (distinct))
        eqs (if (some false-e? eqs)
              [(false-e)]
              (vec eqs))]
    (cond
      (> (count eqs) 1) [:ande eqs]
      (= (count eqs) 1) (first eqs)
      :else (true-e))))

(s/fdef => :args (s/cat :p ::equation :q ::equation) :ret ::equation)
(defn =>
  "implies. If the first equation is true then the second must be true."
  [p q]
  [:imp p q])

(defn get-eqs
  [e]
  (nth e 1))

(defn eq-tag [e]
  (nth e 0))

(instrument-ns)
