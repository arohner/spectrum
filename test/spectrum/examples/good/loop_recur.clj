(ns spectrum.examples.good.recur
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :x string?) :ret string?)
(defn foo [x]
  (loop [x x]
    (if (= "bob")
      x
      (recur x))))
