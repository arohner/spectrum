(ns spectrum.integration-test
  (:require [clojure.test :refer :all]
            [clojure.spec.alpha :as s]
            [spectrum.conform :as c]
            [spectrum.check :as check]))

(deftest forms
  (testing "truthy"
    (are [form args expected] (c/valid? expected (check/type-of form args))

      ;;; invoke
      '(:foo {:foo 1}) {} (c/value 1)
      '({:foo 1} :foo) {} (c/value 1)
      '({:foo 1} :bar) {} (c/value nil)
      '({:foo 1} :bar :baz) {} (c/value :baz)
      '(:bar {:foo 1} :baz) {} (c/value :baz)
      '(:foo 1) {} (c/value nil)
      '(:foo 1 2) {} (c/value 2)
      '([:a :b :c] 1) {} (c/value :b)
      '(#{:a :b :c} :c) {} (c/value :c)
      '(#{:a :b :c} :d) {} (c/value nil)
      '(x :foo) {:x (c/parse-spec (s/map-of keyword? string?))} (c/or- [(c/pred-spec #'string?) (c/value nil)])
      '(x :foo) {:x (c/parse-spec (s/map-of string? string?))} (c/value nil)
      '(:foo x) {:x (c/value {:foo 1})} (c/value 1)
      '(:foo x) {:x (c/parse-spec (s/map-of keyword? string?))} (c/or- [(c/pred-spec #'string?) (c/value nil)])
      '(:foo x) {:x (c/parse-spec (s/map-of string? string?))} (c/value nil)
      '(string? x) {:x (c/value "foo")} (c/value true)
      '((var string?) x) {:x (c/value "foo")} (c/value true)


      ;; map
      '(map inc (range 5)) {} (c/coll-of (c/or- [(c/class-spec Long) (c/class-spec clojure.lang.BigInt)])) ; todo ann range to return more precise types when start & end are known
      '(map even? (range 5)) {} (c/coll-of (c/pred-spec #'boolean?))))
  (testing "falsey"
    (are [form args] (c/invalid? (check/type-of form args))
      ;; invoke arity
      '(string? "foo" "bar") {}
      '((fn [x] (inc x)) "foo" "bar") {}
      '(let [x (fn [y] (inc y))] (x "foo" "bar")) {}
      '(let [x (fn [y] (inc y))] (x)) {}
      '(*print-level* :foo) {})))
