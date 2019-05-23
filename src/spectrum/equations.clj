(ns spectrum.equations
  (:require [clojure.spec.alpha :as s]
            [spectrum.types :as t]
            [spectrum.util :refer [instrument-ns]]))

(s/def ::equality (s/tuple #{:eq} ::t/fresh-type ::t/fresh-type))
(s/fdef eq :args (s/cat :x ::t/type :y ::t/type) :ret ::equality)
(defn eq [x y]
  "constraint that (valid? x y) should be true"
  [:eq x y])

(s/def ::test ::equality)
(s/def ::then ::equality)

(s/def ::conde! (s/tuple #{:conde!} (s/map-of ::test ::then)))
(s/fdef conde! :args (s/cat :p (s/map-of ::test ::then)) :ret ::conde!)
(defn conde!
  "Take a map of `test` `then` key/values. Tests _may_ unify, but isn't
  required. If a `test` unifies, its `then` _must_ unify. Fails if
  no `test` unifies"
  [pairs]
  [:conde! pairs])

(defn conde? [x]
  (and (vector? x)
       (= :conde! (nth x 0))))

(s/def ::equation (s/or :eq ::equality :conde! ::conde!))
(s/def ::equations (s/coll-of ::equation))

(instrument-ns)
