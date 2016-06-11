(ns spectrum.examples.bad.invoke-wrong-type
  (:require [clojure.spec :as s]))

(s/fdef foo :args (s/cat :x keyword?) :ret string?)

(defn foo [x]
  "foo")

(s/fdef bad :args empty? :ret string?)
(defn bad []
  (foo 3))
