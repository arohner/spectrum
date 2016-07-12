(ns spectrum.examples.good.defn
  (:require [clojure.spec :as s]))

(s/fdef foo :args int? :ret int?)

(defn foo [x]
  (inc x))
