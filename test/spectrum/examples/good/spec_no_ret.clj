(ns spectrum.examples.good.spec-no-ret
  (:require [clojure.spec.alpha :as s]))

;; no :ret, should get no error
(s/fdef foo :args (s/cat :x string?))
(defn foo [x]
  x)
