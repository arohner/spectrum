(ns spectrum.examples.good.defn
  (:require [clojure.spec :as s]))

(s/fdef foo :args integer? :ret integer?)

(defn foo [x]
  (inc x))
