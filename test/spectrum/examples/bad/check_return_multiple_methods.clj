(ns spectrum.examples.bad.check-return
  (:require [clojure.spec :as s]))


(s/fdef foo :args (s/cat :x integer? :y (s/? integer?)) :ret string?)
(defn foo
  ([x]
   "foo")
  ([x y]
   (+ x y)))
