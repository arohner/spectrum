(ns spectrum.examples.good.defprotocol-defrecord
  (:require [clojure.spec :as s]))

(defprotocol Foo
  (foo [this x]))

(s/fdef foo :args (s/cat :obj any? :x int?) :ret int?)

(defrecord Bar []
  Foo
  (foo [this x]
    (inc x)))
