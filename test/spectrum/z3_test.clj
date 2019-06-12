(ns spectrum.z3-test
  (:require [clojure.test :refer :all]
            [spectrum.z3 :as z3 :refer [q]]))

(def a :a)
(def b :b)

(deftest q-works
  (are [in out] (= out in)
    (q (foo ~a)) '(foo :a)
    (q (foo ~a ~b)) '(foo :a :b)
    (let [bar [1 2 3]]
      (q (foo ~@bar))) '(foo 1 2 3)
    (let [bar [1 2 3]]
      (q (foo ~@bar ~a))) '(foo 1 2 3 :a)
    (let [bar [1 2 3]
          bbq [:bbq]]
      (q (foo ~@bar ~@bbq))) '(foo 1 2 3 :bbq)))

(deftest eval-works
  (is (coll? (z3/eval (z3/new-context) '(get-info :version)))))

(deftest smt-fns-work
  (is (coll? (z3/get-info :version))))
