(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
            [clojure.set :as set]
            [spectrum.conform :as c]
            [spectrum.types :as t])
  (:import [clojure.lang Keyword]))

(def a?)
(def b?)
(def c?)

(deftest occurs?
  (testing "truthy"
    (are [x y subst] (= true (c/occurs? x y subst))
      '?x ['seq-of '?x] {}
      '?x '?y {'?y '?x}
      ))
  (testing "falsey"
    (are [x y subst] (not (c/occurs? x y subst))
      '?x '?y {}
      '?t1 ['or #{'?k #'char?}] {'?k '?x, '?x ['or #{'?k #'char?}]}
      )))

(deftest accept-nil?
  (testing "truthy"
    (are [t] (c/accept-nil? t)
      (t/? #'int?)
      (t/value-t [])))
  (testing "falsey"
    (are [t] (not (c/accept-nil? t))
      (t/cat-t [#'int?])
      (t/value-t [3]))))

(deftest unify
  (testing "truthy"
    (are [x y subst] (= (set subst) (set (c/unify x y)))
      ;; or
      (t/or-t ['?a '?b]) '?a '[{} {?b ?a}]
      (t/or-t ['?a '?b]) '?x '[{?a ?x} {?b ?x}]
      (t/or-t [#'int?]) '?x [{'?x #'int?}]

      (t/or-t ['?a '?b]) #'int? [{'?a #'int?}
                                 {'?b #'int?}]

      (t/or-t ['?a '?b]) (t/or-t [#'int? #'string?]) [{'?a #'clojure.core/int?}
                                                      {'?b #'clojure.core/int?}
                                                      {'?a #'clojure.core/string?}
                                                      {'?b #'clojure.core/string?}]

      (t/or-t ['?x '?y '?z]) (t/or-t ['?a '?b]) '#{{?x ?b} {?y ?b} {?x ?a} {?y ?a} {?z ?b} {?z ?a}}

      ;; cat
      (t/cat-t [(t/? '?a)]) (t/cat-t [(t/? #'int?)]) [{'?a #'int?}
                                                      {}]

      (t/cat-t [(t/seq-of '?a)]) (t/cat-t [(t/seq-of #'int?)]) [{} {'?a #'int?}]

      ['cat ['seq-of '?x]] ['cat '?y] [{'?y ['seq-of '?x]}]


      ))

  (testing "truthy substs"
    (are [x y substs-in] (seq (c/unify x y substs-in))
      '?a '?b [{'?a (t/or-t ['?b '?c])}]))

  (testing "substs in out"
    (are [x y in out] (= out (c/unify x y in))
      ;; narrowing
      #'seqable? '?x [{'?x #'any?}] [{'?x #'seqable?}]
      ['seq-of '?x] ['seq-of '?y] [{'?x #'string? '?y #'any?}] [{'?x #'string? '?y #'string?}]

      #'seqable? '?x [{'?x #'int?}] nil
      ['seq-of '?x] ['seq-of '?y] [{'?x #'string? '?y #'int?}] nil))

  (testing "substs contains"
    (are [x y substs] (= substs (set/intersection substs (set (c/unify x y))))
      '?x ['value :foo] #{{'?x #'keyword?}
                          {'?x (t/value-t :foo)}}))

  (testing "substs ="
    (are [x y substs] (= (set substs) (set (c/unify x y)))
      '?x ['and #{'?y #'clojure.core/chunked-seq?}] [{'?x ['and #{'?y #'chunked-seq?}]}]
      '[cat ?a [cat ?b]] '[cat ?c ?d] '[{?a ?c, ?b ?d}]))

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
  (are [x y ret] (do
                   (println "ct/dx" x y)
                   (= ret (c/dx x y [{}])))

    (t/cat-t [#'a?]) #'a? [{:state nil :substs [{}]}]
    ;; (t/cat-t [#'string?]) (t/value-t ["foo"]) [{:state nil :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'a? [{:state (t/cat-t [#'b?]) :substs [{}]}
                                           {:state (t/cat-t [(t/seq-of #'a?) #'b?]) :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'b? [{:state nil :substs [{}]}]

    ;; (t/value-t ["foo"]) (t/value-t ["foo"]) [{:state nil :substs [{}]}]
    ))

(deftest valid?
  (testing "truthy"
    (are [x y] (do
                 (println "valid?" x y)
                 (= true (c/valid? x y)))
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

      ;; and
      #'string? (t/and-t ['?x #'string?])
      (t/and-t ['?x '?y]) (t/and-t ['?x '?y '?z])
      #'int? (t/and-t [#'int? #'even?])

      ;; not
      (t/not-t #'string?) #'int?
      (t/not-t #'string?) '?x
      '?x (t/not-t #'string?)
      #'int? (t/and-t [#'int? (t/not-t #'even?)])

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

      (t/or-t [(t/cat-t [#'a?]) (t/cat-t [#'b?])]) (t/cat-t [(t/or-t [#'a? #'b?])])

      ;; seq-of
      (t/seq-of #'a?) (t/cat-t [])
      (t/seq-of #'a?) (t/cat-t [#'a?])
      (t/seq-of #'a?) (t/cat-t [#'a? #'a?])

      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a? #'b?])

      (t/or-t #{(t/cat-t ['?x (t/seq-of '?y)]) (t/cat-t ['?x])}) (t/cat-t ['?x])

      ;; ;; value
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
      ;; and
      (t/and-t ['?x '?y]) '?x

      ;;not
      #'int? (t/not-t #'int?)
      #'int? (t/not-t #'string?)
      #'int? (t/not-t #'even?) ;; could be string
      #'int? (t/and-t [#'any? (t/not-t #'string?)])

      ;; cat
      (t/cat-t [#'b?]) (t/cat-t [#'a?])
      (t/cat-t [#'b?]) (t/cat-t [#'b? #'b?])
      ;; ?

      ;; seq
      (t/seq-of #'a?) (t/seq-of #'b?)
      (t/seq-of #'b?) (t/cat-t [#'a?])
      ['seq-of #'int?] #'int?
      ['seq-of '?a] #'any?
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
