(ns spectrum.examples.good.recur
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :i integer?) :ret even?)
(defn foo [x]
  (if (even? x)
    x
    (recur (inc x))))
