(ns spectrum.examples.bad.multi-method-bad-return
  (:require [clojure.spec.alpha :as s]))

(s/fdef foo :args (s/cat :x any?) :ret string?)

(defmulti foo class)

(defmethod foo Number [x]
  "correct")

(defmethod foo String [x]
  :bogus)
