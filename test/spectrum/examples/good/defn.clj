(ns spectrum.examples.good.defn
  (:require [clojure.spec :as s]))

(s/fdef foo :args (s/cat :x int?) :ret int?)

(defn foo [x]
  (inc x))
