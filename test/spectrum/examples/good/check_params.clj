(ns spectrum.examples.good.check-params
  (:require [clojure.spec :as s]))

(s/fdef foo :args (s/cat :x int?) :ret int?)
(defn foo [x]
  x)
