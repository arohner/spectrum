(ns spectrum.unify-test
  (:require [clojure.test :refer :all]
            [spectrum.conform :as c]
            [spectrum.unify :as u]))

(deftest unifier-works
  (testing "truthy"
    (are [a b] (map? (u/unify a b))
      '?x 3
      ['?x] [1]
      '?x 1
      nil nil
      '_ '?x
      #{:foo :bar} #{:foo :bar}
      {:a :b} {:a :b}
      {:a :b} {:a '?b}
      {:a '?b} {:a :b}
      {:a '?b} {:a '?b}
      {'?a '?b} {:a '?b}

      (u/contains #{:foo :bar}) :foo
      (u/contains [:foo :bar]) :foo
      (u/contains #{:foo '?x}) '?x
      :foo (u/contains #{:foo '?x})
      (u/submap {:foo '?x}) {:foo '?x :bar '?y}
      (u/submap {'?x :bar}) {:foo :bar}
      #{:foo} #{'?x}
      #{} #{}
      '(map-of ?x ?y) '(map-of ?t string?))

  (testing "falsey"
    (are [a b] (= nil (u/unify a b))
      1 2
      [1] [2]
      ['?x] [1 2]
      #{} []
      #{:foo} :bar
      :bar #{:foo}
      #{:foo :bar} '#{?x}))))
