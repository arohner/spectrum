(ns spectrum.examples.bad.invoke-wrong-type
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args keyword? :ret string?)

(defn foo [x]
  "foo")

(defn bad []
  (foo 3))
