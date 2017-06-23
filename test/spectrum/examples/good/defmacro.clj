(ns spectrum.examples.good.defmacro
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :x int?))

(defmacro foo [x]
  `(inc x))
