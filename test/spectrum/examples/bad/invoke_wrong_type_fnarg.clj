(ns spectrum.examples.bad.invoke-wrong-type-fnarg
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :x keyword?) :ret string?)

(defn foo [x]
  "foo")

(s/fdef bad :args (s/cat :x integer?) :ret string?)
(defn bad [x]
  (foo x))
