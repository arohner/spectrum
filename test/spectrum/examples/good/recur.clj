(ns spectrum.examples.good.recur
  (:require [clojure.spec :as s]))

(s/fdef foo :args (s/cat :i int?) :ret even?)
(defn foo [x]
  (if (even? x)
    x
    (recur (inc x))))
