(ns spectrum.examples.bad.spec-not-match-arity
  (:require [clojure.spec.alpha :as s]))


;; fn takes two args, spec takes one.

(s/fdef foo :args (s/cat :a integer?) :ret integer?)
(defn foo [a b]
  (+ a b))
