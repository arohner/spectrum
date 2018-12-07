(ns spectrum.unify-test
  (:require [clojure.test :refer :all]
            [spectrum.unify :as u]))

(deftest unifier-works
  (testing "truthy"
    (are [a b] (map? (u/unify a b))
      '?x 3
      ['?x] [1]
      '?x 1
      '(map-of ?x ?y) '(map-of ?t string?)
      (c/map-of (c/new-logic 'x) (c/new-logic 'y)) (c/map-of (c/pred-spec #'int?) (c/pred-spec #'string?)))

  (testing "falsey"
    (are [a b] (= nil (u/unify a b))
      1 2
      [1] [2]
      ['?x] [1 2]))))
