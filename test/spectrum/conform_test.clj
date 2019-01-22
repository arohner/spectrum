(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
            [clojure.set :as set]
            [spectrum.conform :as c]
            [spectrum.types :as t])
  (:import [clojure.lang Keyword]))

(def a?)
(def b?)
(def c?)

(deftest unify
  (testing "truthy"
    (are [x y subst] (= (set subst) (set (c/unify x y)))
      ;; or
      (t/or-t ['?a '?b]) '?a '[{} {?b ?a}]
      (t/or-t ['?a '?b]) '?x '[{?a ?x} {?b ?x}]
      (t/or-t [#'int?]) '?x [{'?x #'int?}]

      (t/or-t ['?a '?b]) #'int? [{'?a #'int?}
                                 {'?b #'int?}]

      (t/or-t ['?a '?b]) (t/or-t [#'int? #'string?]) [{'?a #'int? '?b #'string?}
                                                      {'?a #'string? '?b #'int?}]

      (t/or-t ['?x '?y '?z]) (t/or-t ['?a '?b]) '[{?x ?b, ?b ?a}
                                                  {?z ?a, ?a ?b}
                                                  {?x ?a, ?z ?b}
                                                  {?y ?a, ?z ?b}
                                                  {?x ?a, ?a ?b}
                                                  {?y ?a, ?x ?b}
                                                  {?x ?a, ?y ?b}
                                                  {?y ?b, ?b ?a}
                                                  {?z ?b, ?b ?a}
                                                  {?z ?a, ?x ?b}
                                                  {?z ?a, ?y ?b}
                                                  {?y ?a, ?a ?b}]

      ;; cat
      (t/cat-t [(t/? '?a)]) (t/cat-t [(t/? #'int?)]) [{'?a #'int?}
                                                      {'?a nil}
                                                      {}]

      (t/cat-t [(t/seq-of '?a)]) (t/cat-t [(t/seq-of #'int?)]) [{} {'?a nil} {'?a #'int?}]
      ))

  (testing "truthy substs"
    (are [x y substs-in] (seq (c/unify x y substs-in))
      '?a '?b [{'?a (t/or-t ['?b '?c])}]))

  (testing "substs contains"
    (are [x y substs] (= substs (set/intersection substs (set (c/unify x y))))
      '?x ['value :foo] #{{'?x #'keyword?}
                          {'?x (t/value-t :foo)}}))

  (testing "falsey"
    (are [x y] (nil? (c/unify x y))
      (t/or-t [#'int? #'string?]) #'keyword?)))

(deftest first-t
  (are [t ret] (= (set ret) (set (c/first-t t)))
    (t/seq-of #'a?) [#'a? nil]
    (t/cat-t [(t/seq-of #'a?) #'b?]) [#'a? #'b?]
    (t/cat-t [(t/seq-of #'a?) (t/? #'b?)]) [#'a? #'b? nil]))

(deftest dx?
  (testing "truthy"
    (are [t] (c/dx? t)
      (t/cat-t [])
      (t/cat-t [#'int?])
      (t/value-t [1 2 3])))
  (testing "falsey"
    (are [t] (= false (c/dx? t))
      #'int?)))

(deftest dx
  (are [x y ret] (= ret (c/dx x y [{}]))
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'a? [{:state (t/cat-t [#'b?]) :substs [{}]}
                                           {:state (t/cat-t [(t/seq-of #'a?) #'b?]) :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'b? [{:state nil :substs [{}]}]))

(deftest valid?
  (testing "truthy"
    (are [x y] (= true (c/valid? x y))
      '?x 3
      ['?x] [1]
      nil nil
      '_ '?x
      #'any? #'a?
      #{:foo :bar} #{:foo :bar}
      {:a :b} {:a :b}
      {:a :b} {:a '?b}
      {:a '?b} {:a :b}
      {:a '?b} {:a '?b}
      {'?a '?b} {:a '?b}
      #'any? (t/seq-of '?x)

      '?x '?x
      '?y '?y

      ;; or
      (t/or-t #{'?a}) '?a
      (t/or-t #{#'a? #'b?}) #'a?
      (t/or-t #{#'a? #'b?}) (t/or-t #{#'a? #'b?})
      (t/or-t #{#'a? '?x}) #'a?
      (t/or-t #{#'a? '?x}) '?x

      ;; cat
      (t/cat-t []) (t/cat-t [])
      (t/cat-t [#'a?]) (t/cat-t [#'a?])
      (t/cat-t [#'a? #'a?]) (t/cat-t [#'a? #'a?])

      (t/cat-t ['?x]) (t/cat-t ['?x])
      (t/cat-t [(t/* '?x)]) (t/cat-t ['?x])
      (t/cat-t [(t/+ '?x)]) (t/cat-t ['?x])

      ;; ?
      (t/cat-t [(t/? #'b?)]) (t/cat-t [#'b?])
      (t/cat-t [#'a? (t/? #'b?) #'a?]) (t/cat-t [#'a? #'a?])
      (t/cat-t [#'a? (t/? #'b?) #'a?]) (t/cat-t [#'a? #'b? #'a?])

      ;; seq-of
      (t/seq-of #'a?) (t/cat-t [])
      (t/seq-of #'a?) (t/cat-t [#'a?])
      (t/seq-of #'a?) (t/cat-t [#'a? #'a?])

      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a? #'b?])

      (t/or-t #{(t/cat-t ['?x (t/seq-of '?y)]) (t/cat-t ['?x])}) (t/cat-t ['?x])

      ;; value
      '?x (t/value-t 3)
      :foo (t/value-t :foo)
      (t/value-t 3) '?x
      #'int? (t/value-t 3)
      #'string? (t/value-t "foo")
      (t/seq-of (t/class-t Character)) (t/value-t "foo")
      (t/cat-t [#'int? #'string?]) (t/value-t [3 "foo"])
      (t/cat-t [(t/cat-t [#'int?]) #'string?]) (t/value-t [3 "foo"])
      (t/cat-t [(t/spec-t (t/cat-t [#'int?])) #'string?]) (t/value-t [[3] "foo"])

      '?a '[invoke ?x [cat ?y]]
      ))

  (testing "falsey"
    (are [x y] (= false (c/valid? x y))
      1 2
      [1] [2]
      ['?x] [1 2]
      #{} []
      #{:foo} :bar
      :bar #{:foo}
      #'a? #'b?
      (t/vector-of '?x) (t/seq-of '?x)
      (t/coll-of #'a?) (t/vector-of #'b?)
      #'a? (t/or-t #{#'a? #'b?})

      ;; or
      (t/or-t #{#'a? #'b?}) #'c?
      ;; cat
      (t/cat-t [#'b?]) (t/cat-t [#'a?])
      (t/cat-t [#'b?]) (t/cat-t [#'b? #'b?])
      ;; ?

      ;; seq
      (t/seq-of #'b?) (t/cat-t [#'a?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a?])

      (t/class-t Integer) (t/class-t Keyword)

      ;; value
      #'string? (t/value-t 3)

      (t/cat-t [#'int? #'string?]) [3 "foo"] ;; missing value-t
      (t/cat-t [#'int? #'string?]) (t/value-t [[3] "foo"])
      )))

(deftest and-logic
  (are [ts ret] (= ret (t/and-t ts))
    ['?x] '?x
    ['?x '?y] ['and #{'?x '?y}]
    [['maybe '?y]] '?y
    ['?x ['maybe '?y]] ['or #{'?x '?y}]
    [#'any?] #'any?
    ['?x '?y ['maybe '?z]] ['or #{['and #{'?x '?y}] '?z}]))

(deftest or-logic
  (are [ts ret] (= ret (t/or-t ts))
    ['?x] '?x
    ['?x '?y] ['or #{'?x '?y}]
    ['?x ['or #{'?y '?z}]] ['or #{'?x '?y '?z}]
    ['?x ['maybe '?y]] ['or #{'?x '?y}]
    [['maybe '?y]] '?y))

(deftest apply-invoke
  (let [s (t/fn-t {[#'nil?] #'nil?
                   [#'string?] #'symbol?
                   [#'keyword?] #'keyword?})]
    (testing "truthy"
      (are [f args ret] (= ret (c/apply-invoke (t/invoke-t f (t/cat-t args)) [{}]))
        s [#'string?] [[#'symbol? {}]]))
    (testing "falsey"
      (are [f args] (nil? (seq (c/apply-invoke (t/invoke-t f (t/cat-t args)) [{}])))
        s [#'int?]
        s [#'string? #'string?]))))
