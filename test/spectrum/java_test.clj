(ns spectrum.java-test
  (:require [clojure.test :refer :all]
            [spectrum.java :as j]))

(deftest resolve-java-class-works
  (are [x result] (= result (j/resolve-java-class x))
    'long Long/TYPE
    "char" Character/TYPE
    'java.lang.Long Long
    String String
    'java.lang.Object<> (class (into-array Object []))))
