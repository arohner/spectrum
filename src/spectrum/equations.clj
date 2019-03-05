(ns spectrum.equations
  (:require [clojure.spec.alpha :as s]
            [spectrum.types :as t]
            [spectrum.util :refer [instrument-ns]]))

(s/def ::equality (s/tuple #{:eq} ::t/type ::t/type))
(s/fdef eq :args (s/cat :x ::t/type :y ::t/type) :ret ::equality)
(defn eq [x y]
  "constraint that (valid? x y) should be true"
  [:eq x y])

(s/def ::test ::equality)
(s/def ::then ::equality)
(s/def ::conde (s/tuple #{:conde} ::test ::then))
(s/fdef conde :args (s/cat :test ::test :then ::then) :ret ::conde)

(defn conde [test then]
  "constraint that when the equation `test` is true, `then` must also
  be true. One-way, does not imply that when `then` is true, `test`
  must be true. "
  [:conde test then])

(s/def ::conde! (s/tuple #{:conde!} (s/map-of ::test ::then)))
(s/fdef conde! :args (s/cat :p (s/map-of ::test ::then)) :ret ::conde!)
(defn conde!
  "Take a map of `when` `then` keyvalues. Behaves similar to conde, but
  fails if no `test` unifies"
  [pairs]
  [:conde! pairs])

(s/def ::equation (s/or :eq ::equality :conde ::conde :conde! ::conde!))
(s/def ::equations (s/coll-of ::equation))

(instrument-ns)
