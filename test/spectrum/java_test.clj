(ns spectrum.java-test
  (:require [clojure.test :refer :all]
            [spectrum.java :as j]))

(deftest resolve-java-class-works
  (are [x result] (= result (j/resolve-java-class x))
    'long Long
    "char" Character
    String String))
