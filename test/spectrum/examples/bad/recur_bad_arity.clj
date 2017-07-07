(ns spectrum.examples.bad.loop-change-type
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :i int?) :ret int?)
(defn foo [x]
  (let [y 3]
    (if (even? x)
      (recur x y)
      (inc x))))
