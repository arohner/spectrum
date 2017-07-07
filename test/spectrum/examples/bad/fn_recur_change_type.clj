(ns spectrum.examples.bad.loop-change-type
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :i int?) :ret int?)
(defn foo [x]
  (if (even? x)
    (recur (str x))
    (inc x)))
