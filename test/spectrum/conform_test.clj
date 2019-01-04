(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
            [spectrum.conform :as c]))

(def a?)
(def b?)
(def c?)

(deftest unify
  (testing "truthy"
    (are [x y subst] (= (set subst) (set (c/unify x y)))
      ;; or
      (c/or-t ['?a '?b]) '?a '[{} {?a ?b}]
      (c/or-t ['?a '?b]) '?x '[{?x ?a} {?x ?b}]
      (c/or-t [#'int?]) '?x [{'?x #'int?}]

      (c/or-t ['?a '?b]) #'int? [{'?a #'int?}
                                 {'?b #'int?}]

      (c/or-t ['?a '?b]) (c/or-t [#'int? #'string?]) [{'?a #'int? '?b #'string?}
                                                      {'?a #'string? '?b #'int?}]

      (c/or-t ['?x '?y '?z]) (c/or-t ['?a '?b]) '[{?a ?x, ?b ?x}
                                                  {?a ?y, ?b ?x}
                                                  {?a ?z, ?b ?x}
                                                  {?a ?x, ?b ?y}
                                                  {?a ?y, ?b ?y}
                                                  {?a ?z, ?b ?y}
                                                  {?a ?x, ?b ?z}
                                                  {?a ?y, ?b ?z}
                                                  {?a ?z, ?b ?z}]

      ;; cat
      (c/cat-t [(c/? '?a)]) (c/cat-t [(c/? #'int?)]) [{'?a #'int?}
                                                      {'?a nil}
                                                      {}]))

  (testing "falsey"
    (are [x y] (nil? (c/unify x y))
      (c/or-t [#'int? #'string?]) #'keyword?)))

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
      #'any? (c/seq-of '?x)
      #'any? #'integer?
      #'integer? #'int?
      #'number? #'even?
      '?x '?x
      '?y '?y

      (c/seq-of '?x) (c/seq-of '?x)
      (c/seq-of '?z) (c/seq-of '?z)
      #'seqable? (c/seq-of '?x)
      (c/coll-of '?x) (c/vector-of '?x)
      (c/coll-of #'a?) (c/vector-of #'a?)

      ;; or
      (c/or-t #{'?a}) '?a
      (c/or-t #{#'a? #'b?}) #'a?
      (c/or-t #{#'a? #'b?}) (c/or-t #{#'a? #'b?})
      (c/or-t #{#'a? '?x}) #'a?
      (c/or-t #{#'a? '?x}) '?x

      ;; cat
      (c/cat-t []) (c/cat-t [])
      (c/cat-t [#'a?]) (c/cat-t [#'a?])
      (c/cat-t [#'a? #'a?]) (c/cat-t [#'a? #'a?])

      (c/cat-t ['?x]) (c/cat-t ['?x])
      (c/cat-t [(c/* '?x)]) (c/cat-t ['?x])
      (c/cat-t [(c/+ '?x)]) (c/cat-t ['?x])
      (c/seq-of #'a?) (c/cat-t [#'a? #'a?])

      ;; ?
      (c/cat-t [(c/? #'b?)]) (c/cat-t [#'b?])
      (c/cat-t [#'a? (c/? #'b?) #'a?]) (c/cat-t [#'a? #'a?])
      (c/cat-t [#'a? (c/? #'b?) #'a?]) (c/cat-t [#'a? #'b? #'a?])

      ;; seq-of
      (c/seq-of #'a?) (c/cat-t [])
      (c/seq-of #'a?) (c/cat-t [#'a?])
      (c/seq-of #'a?) (c/cat-t [#'a? #'a?])

      (c/cat-t [(c/seq-of #'a?) #'b?]) (c/cat-t [#'b?])
      (c/cat-t [(c/seq-of #'a?) #'b?]) (c/cat-t [#'a? #'b?])
      (c/cat-t [(c/seq-of #'a?) #'b?]) (c/cat-t [#'a? #'a? #'b?])))
  (testing "falsey"
    (are [x y] (= false (c/valid? x y))
      1 2
      [1] [2]
      ['?x] [1 2]
      #{} []
      #{:foo} :bar
      :bar #{:foo}
      #'a? #'b?
      (c/vector-of '?x) (c/seq-of '?x)
      (c/coll-of #'a?) (c/vector-of #'b?)
      #'a? (c/or-t #{#'a? #'b?})

      ;; or
      (c/or-t #{#'a? #'b?}) #'c?
      ;; cat
      (c/cat-t [#'b?]) (c/cat-t [#'a?])
      (c/cat-t [#'b?]) (c/cat-t [#'b? #'b?])
      (c/cat-t [#'a? #'a?]) (c/seq-of #'a?)
      ;; ?

      ;; seq
      (c/seq-of #'b?) (c/cat-t [#'a?])
      (c/cat-t [(c/seq-of #'a?) #'b?]) (c/cat-t [#'a? #'a?]))))

(deftest and-logic
  (are [ts ret] (= ret (c/and-t ts))
    ['?x] '?x
    ['?x '?y] ['and #{'?x '?y}]
    [['maybe '?y]] '?y
    ['?x ['maybe '?y]] ['or #{'?x '?y}]
    [#'int? #'any?] #'int?
    [#'any?] #'any?
    ['?x '?y ['maybe '?z]] ['or #{['and #{'?x '?y}] '?z}]))

(deftest or-logic
  (are [ts ret] (= ret (c/or-t ts))
    ['?x] '?x
    ['?x '?y] ['or #{'?x '?y}]
    ['?x ['or #{'?y '?z}]] ['or #{'?x '?y '?z}]
    ['?x ['maybe '?y]] ['or #{'?x '?y}]
    [['maybe '?y]] '?y))

(deftest fix-length
  (are [t n ret] (= ret (c/fix-length t n))
    (c/* '?t) 2 [(c/cat-t []) (c/cat-t ['?t]) (c/cat-t ['?t '?t])]

    (c/cat-t []) 2 [(c/cat-t [])]
    (c/cat-t ['?t]) 2 [(c/cat-t ['?t])]
    (c/cat-t [(c/* '?a) '?b]) 2 [(c/cat-t ['?b]) (c/cat-t ['?a '?b])]))

(deftest disentangle
  (are [t ret] (= ret (c/disentangle t))
    (c/cat-t [(c/? '?t1) '?t2]) [(c/cat-t ['?t1 '?t2]) (c/cat-t ['?t2])]))

(deftest all-possible-values
  (are [t n ret] (= ret (c/all-possible-values t 2))
    (c/cat-t [(c/* '?a) (c/* '?b) (c/? '?c)]) 2 #{(c/cat-t [])
                                                (c/cat-t ['?a])
                                                (c/cat-t ['?b])
                                                (c/cat-t ['?c])
                                                (c/cat-t ['?a '?a])
                                                (c/cat-t ['?a '?b])
                                                (c/cat-t ['?a '?c])
                                                (c/cat-t ['?b '?b])
                                                (c/cat-t ['?b '?c])}
    (c/cat-t []) 0 #{(c/cat-t [])}))

(deftest value-preds
  (are [x y] (seq (c/unify x y))
    (c/value-t nil) #'nil?
    #'nil? (c/value-t nil)
    (c/value-t true) #'true?))
