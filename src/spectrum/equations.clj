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
(s/def ::conde (s/tuple #{:when} ::test ::then))
(s/fdef conde :args (s/cat :when ::when :test ::test) :ret ::conde)
(defn conde [when then]
  "constraint that when the equation `when` is true, `then` must also be true. one-way, does not imply that when `then` is true, `when` must be true"
  [:when when then])

(s/def ::equation (s/or :eq ::equality :cond ::conde))
(s/def ::equations (s/coll-of ::equation))

(instrument-ns)
