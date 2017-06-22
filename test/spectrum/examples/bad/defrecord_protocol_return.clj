(ns spectrum.examples.bad.defrecord-protocol-return
  (:require [clojure.spec.alpha :as s]))

(defprotocol Foo
  (foo [x]))

(s/fdef foo :args (s/cat :x integer?) :ret integer?)

;; return type doesn't match spec, in a protocol method
(defrecord Bar []
  Foo
  (foo [x]
    (str x)))
