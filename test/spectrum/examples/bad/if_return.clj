(ns spectrum.examples.bad.if-return
  (:require [clojure.spec :as s]))

;; if should return (or int? string?), falsifying :ret string?

(s/fdef foo :args (s/cat :x integer?) :ret string?)
(defn foo [x]
  (if (even? (rand-int 2))
    (+ x 1)
    "foo"))
