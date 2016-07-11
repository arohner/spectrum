(ns spectrum.examples.bad.check-return
  (:require [clojure.spec :as s]))


(s/fdef foo :args (s/cat :x integer?) :ret string?)
(defn foo [x]
  (+ x 1))
