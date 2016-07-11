(ns spectrum.examples.bad.invoke-let
  (:require [clojure.spec :as s]))

(defn foo []
  (let [x (+ 1 2)]
    (name x)))
