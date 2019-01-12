(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
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
      (t/or-t ['?a '?b]) '?a '[{} {?a ?b}]
      (t/or-t ['?a '?b]) '?x '[{?x ?a} {?x ?b}]
      (t/or-t [#'int?]) '?x [{'?x #'int?}]

      (t/or-t ['?a '?b]) #'int? [{'?a #'int?}
                                 {'?b #'int?}]

      (t/or-t ['?a '?b]) (t/or-t [#'int? #'string?]) [{'?a #'int? '?b #'string?}
                                                      {'?a #'string? '?b #'int?}]

      (t/or-t ['?x '?y '?z]) (t/or-t ['?a '?b]) '[{?a ?x, ?b ?x}
                                                  {?a ?y, ?b ?x}
                                                  {?a ?z, ?b ?x}
                                                  {?a ?x, ?b ?y}
                                                  {?a ?y, ?b ?y}
                                                  {?a ?z, ?b ?y}
                                                  {?a ?x, ?b ?z}
                                                  {?a ?y, ?b ?z}
                                                  {?a ?z, ?b ?z}]

      ;; cat
      (t/cat-t [(t/? '?a)]) (t/cat-t [(t/? #'int?)]) [{'?a #'int?}
                                                      {'?a nil}
                                                      {}]

      (t/cat-t [(t/seq-of '?a)]) (t/cat-t [(t/seq-of #'int?)]) [{} {'?a nil} {'?a #'int?}]))

  (testing "falsey"
    (are [x y] (nil? (c/unify x y))
      (t/or-t [#'int? #'string?]) #'keyword?)))

(deftest first-t
  (are [t ret] (= (set ret) (set (c/first-t t)))
    (t/seq-of #'a?) [#'a? nil]
    (t/cat-t [(t/seq-of #'a?) #'b?]) [#'a? #'b?]
    (t/cat-t [(t/seq-of #'a?) (t/? #'b?)]) [#'a? #'b? nil]))

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
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a? #'b?])))

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

(deftest fix-length
  (are [t n ret] (= ret (c/fix-length t n))
    (t/* '?t) 2 [(t/cat-t []) (t/cat-t ['?t]) (t/cat-t ['?t '?t])]

    (t/cat-t []) 2 [(t/cat-t [])]
    (t/cat-t ['?t]) 2 [(t/cat-t ['?t])]
    ;; (t/cat-t [(t/* '?a) '?b]) 2 [(t/cat-t ['?b]) (t/cat-t ['?a '?b])]
    ))

(deftest disentangle
  (are [t ret] (= ret (c/disentangle t))
    (t/cat-t [(t/? '?t1) '?t2]) [(t/cat-t ['?t1 '?t2]) (t/cat-t ['?t2])]))

(deftest all-possible-values
  (are [t n ret] (= ret (c/all-possible-values t 2))
    (t/cat-t [(t/* '?a) (t/* '?b) (t/? '?c)]) 2 #{(t/cat-t [])
                                                (t/cat-t ['?a])
                                                (t/cat-t ['?b])
                                                (t/cat-t ['?c])
                                                (t/cat-t ['?a '?a])
                                                (t/cat-t ['?a '?b])
                                                (t/cat-t ['?a '?c])
                                                (t/cat-t ['?b '?b])
                                                (t/cat-t ['?b '?c])}
    (t/cat-t []) 0 #{(t/cat-t [])}))

(deftest value-preds
  (are [x y] (seq (c/unify x y))
    (t/value-t nil) #'nil?
    #'nil? (t/value-t nil)
    (t/value-t true) #'true?))

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
