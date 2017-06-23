(ns spectrum.examples.good.set-pred
  (:require [clojure.spec.alpha :as s]))

;; TODO
(s/fdef foo :args (s/cat :x #{:bar :bbq}))
(defn foo [x]
  x)

(foo :bar)
