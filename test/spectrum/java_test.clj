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

(deftest more-specific-works
  (testing "truthy"
    (are [a b] (= true (j/more-specific? a b))
      Long/TYPE Double/TYPE
      Short/TYPE Long/TYPE
      Byte Long/TYPE
      Byte Long
      Byte/TYPE Long
      Long/TYPE Long))

  (testing "false"
    (are [a b] (= false (j/more-specific? a b))
      Double/TYPE Long/TYPE
      Long/TYPE Long/TYPE
      Long Long
      Long/TYPE Byte
      Long Long/TYPE)))

(deftest narrowing-works
  (testing "truthy"
    (are [a b] (= true (j/narrowing? a b))
      Long Byte
      Long/TYPE Byte/TYPE
      Double Long/TYPE
      Double/TYPE Long))

  (testing "false"
    (are [a b] (= false (j/narrowing? a b))
      Long Long
      Double Double/TYPE
      Byte Long
      Byte/TYPE Long/TYPE)))
