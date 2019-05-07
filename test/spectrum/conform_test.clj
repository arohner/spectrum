(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
            [clojure.set :as set]
            [spectrum.conform :as c]
            [spectrum.types :as t])
  (:import [clojure.lang Keyword LazySeq]))

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
      (t/value-t [3])
      (t/value-t nil)
      (t/value-t 1))))

(deftest unify
  (testing "truthy"
    (are [x y subst] (do
                       (println "unify truthy" x y)
                       (= (set subst) (set (c/unify x y))))
      '?a #'int? [{'?a #'int?}]
      ;; or
      (t/or-t ['?a '?b]) '?a '[{}]
      (t/or-t ['?a '?b]) '?x [{'?x (t/or-t ['?a '?b])}]
      (t/or-t [#'int?]) '?x [{'?x #'int?}]

      (t/or-t ['?a '?b]) #'int? [{'?a (t/or-t [#'int? '?a])
                                  '?b (t/or-t [#'int? '?b])}]

      (t/or-t ['?a '?b]) (t/or-t [#'int? #'string?]) [{'?a (t/or-t [#'clojure.core/int? #'clojure.core/string? '?a])
                                                       '?b (t/or-t [#'clojure.core/int? #'clojure.core/string? '?b])}]

      (t/or-t ['?x '?y '?z]) (t/or-t ['?a '?b]) '[{?a [or [?a ?x ?y ?z]]
                                                   ?b [or [?b ?x ?y ?z]]}]

      ;; cat
      (t/cat-t [(t/? '?a)]) (t/cat-t [(t/? #'int?)]) [{'?a ['or [#'int? '?a]]}]

      (t/cat-t [(t/seq-of '?a)]) (t/cat-t [(t/seq-of #'int?)]) [{'?a ['or [#'int? '?a]]}]

      (t/cat-t [(t/seq-of '?x)]) (t/cat-t ['?y]) [{'?y (t/seq-of '?x)}]

      (t/cat-t [(t/seq-of '?x) '?x]) (t/cat-t [#'int? #'int? #'int?]) [{'?x #'int?}]
      ))

  (testing "truthy substs"
    (are [x y substs-in] (seq (c/unify x y substs-in))
      '?a '?b [{'?a (t/or-t ['?b '?c])}]))

  (testing "substs in out"
    (are [x y in out] (do
                        (println "substs in out" x y in out)
                        (= out (c/unify x y in)))
      ;; '?t1 #'nil? [{'?t1 ['or #{#'a? #'nil?}]}] [{'?t1 ['value nil]}]

      ['seq-of '?x] ['seq-of '?y] [{'?x #'string? '?y #'int?}] nil

      ;; fn
      (t/fn-t {['?a] '?b}) (t/fn-t {['?c] '?d ['?e '?f] '?g}) [{}] [{'?c '?a '?d '?b}]

      ;; recursive substs
      '?x ['seq-of #'nil?] [{'?x ['seq-of '?y] '?y ['or #{'?x #'nil?}]}] [{'?x ['seq-of '?y] '?y ['or #{'?x #'nil?}]}]

      ['seq-of '?x] ['seq-of #'nil?] [{'?x '?y '?y ['or #{#'nil? ['seq-of '?x] #'seqable?}]}] [{'?x '?y '?y ['or #{#'nil? ['seq-of '?x] #'seqable?}]}]

      '?x #'b? [{'?x ['seq-of '?y] '?y ['or #{'?x #'nil?}]}] nil
      '?x ['seq-of #'b?] [{'?x ['seq-of '?y] '?y ['or #{'?x #'nil?}]}] nil

      ))

  (testing "substs contains"
    (are [x y substs] (= substs (set/intersection substs (set (c/unify x y))))
      '?x ['value :foo] #{{'?x (t/value-t :foo)}}))

  (testing "substs ="
    (are [x y substs] (= (set substs) (set (c/unify x y)))
      '?x ['and #{'?y #'clojure.core/chunked-seq?}] [{'?x ['and #{'?y #'chunked-seq?}]}]
      '[cat ?a [cat ?b]] '[cat ?c ?d] '[{?c ?a, ?d ?b}]
      '?x '[value nil] [{'?x ['value nil]}]))

  (testing "falsey"
    (are [x y] (nil? (c/unify x y))
      (t/or-t [#'int? #'string?]) #'keyword?)))

(deftest first-t
  (are [t ret] (= (set ret) (set (c/first-t t)))
    (t/seq-of #'a?) [#'a? nil]
    (t/cat-t []) []
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
  (are [x y ret] (= (set ret) (set (c/dx x y [{}])))
    (t/cat-t []) #'a? nil
    (t/cat-t [#'a?]) #'a? [{:state nil :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'a? [{:state (t/cat-t [(t/seq-of #'a?) #'b?]) :substs [{}]}
                                           {:state (t/cat-t [#'b?]) :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'b? [{:state nil :substs [{}]}]

    (t/seq-of (t/class-t Character)) ['value \f] [{:state (t/seq-of (t/class-t Character)) :substs [{}]}
                                                  {:state nil :substs [{}]}]

    #'int? #'int? [{:state nil :substs [{}]}]
    (t/value-t 1) (t/value-t 1) [{:state nil :substs [{}]}]
    (t/cat-t [(t/value-t 1)]) (t/value-t 1) [{:state nil :substs [{}]}]
    ))

(deftest valid?
  (testing "truthy"
    (are [x y] (do
                 (println "valid?" x y)
                 (= true (c/valid? x y)))
      '?x ['value 3]
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
      (t/or-t ['?a]) '?a
      (t/or-t [#'a? #'b?]) #'a?
      (t/or-t [#'a? #'b?]) (t/or-t [#'a? #'b?])
      (t/or-t [#'a? '?x]) #'a?
      (t/or-t [#'a? '?x]) '?x

      ;; and
      #'string? (t/and-t ['?x #'string?])
      (t/and-t ['?x '?y]) (t/and-t ['?x '?y '?z])
      #'int? (t/and-t [#'int? #'even?])
      (t/and-t [#'int? #'number?]) #'int?

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

      ;; seq-of
      (t/seq-of #'a?) (t/cat-t [])
      (t/seq-of #'a?) (t/cat-t [#'a?])
      (t/cat-t [(t/seq-of '?x)]) (t/cat-t ['?y])

      (t/seq-of #'a?) (t/cat-t [#'a? #'a?])

      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'b?])
      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a? #'b?])

      ;; seq string vs char
      (t/seq-of #'char?) ['value "foo"]

      (t/or-t [(t/cat-t ['?x (t/seq-of '?y)]) (t/cat-t ['?x])]) (t/cat-t ['?x])

      ;; ;; value
      '?x (t/value-t 3)
      (t/value-t 3) '?x
      #'int? (t/value-t 3)
      #'string? (t/value-t "foo")
      (t/seq-of (t/class-t Character)) (t/value-t "foo")
      (t/cat-t [#'any?]) (t/cat-t [(t/value-t 1)])
      (t/cat-t [#'int? #'string?]) (t/value-t [3 "foo"])
      (t/cat-t [(t/cat-t [#'int?]) #'string?]) (t/value-t [3 "foo"])

      ;; spec
      (t/spec-t (t/spec-t '?x)) (t/spec-t (t/spec-t '?x))
      (t/spec-t (t/spec-t '?x)) (t/spec-t (t/spec-t '?y))
      (t/cat-t [(t/spec-t (t/seq-of '?x))]) (t/cat-t ['?y])
      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/cat-t [(t/spec-t (t/cat-t [#'int?]))])

      (t/cat-t [(t/spec-t (t/seq-of '?x))]) (t/cat-t [(t/value-t nil)])

      '?a '[invoke ?x [cat ?y]]))

  (testing "falsey"
    (are [x y] (do
                 (println "valid?" x y)
                 (= false (c/valid? x y)))
      1 2
      [1] [2]
      ['?x] [1 2]
      #{} []
      #{:foo} :bar
      :bar #{:foo}
      #'a? #'b?
      (t/vector-of '?x) (t/seq-of '?x)
      (t/coll-of #'a?) (t/vector-of #'b?)
      #'a? (t/or-t [#'a? #'b?])

      ;; or
      (t/or-t [#'a? #'b?]) #'c?
      ;; and
      (t/and-t ['?x '?y]) '?x
      (t/and-t [#'a? #'b? #'c?]) (t/and-t [#'a? #'b?])

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

      (t/value-t nil) (t/seq-of Character)
      (t/value-t 3) 3
      (t/value-t nil) nil

      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/cat-t [#'int?])
      )))

(deftest variance
  (testing "truthy"
    (are [x y in out] (= out (c/unify x y in))
      #'seqable? '?x+ [{'?x+ #'any?}] [{'?x+ #'seqable?}]

      ['seq-of '?x] ['seq-of '?y+] [{'?x #'string? '?y+ #'any?}] [{'?x #'string? '?y+ '?x}]

      #'a? '?x+ [{'?x+ ['or [#'a? #'b?]]}] [{'?x+ #'a?}]

      '?x- #'int? [{'?x- #'string?}] [{'?x- (t/or-t [#'int? #'string?])}]))

  (testing "falsey"
    (are [x y substs] (nil? (c/unify x y substs))
      #'seqable? '?x [{'?x #'any?}]

      ;; ['seq-of ['class java.lang.Character]] '?x+ [{'?x+ ['value nil]}]
      #'seqable? '?x+ [{'?x+ #'int?}])))

(deftest and-logic
  (are [ts ret] (= ret (t/and-t ts))
    ['?x] '?x
    ['?x '?y] ['and ['?x '?y]]
    [#'any?] #'any?

    ;; (t/and-t [#'a? (t/or-t [#'a? #'b?])]) #'a?
    ;; (t/and-t [#'int? (t/or-t [#'even? #'odd?])]) #'a?
    ))

(deftest or-logic
  (are [ts ret] (= ret (t/or-t ts))
    ['?x] '?x
    ['?x '?y] ['or ['?x '?y]]
    ['?x ['or ['?y '?z]]] ['or ['?x '?y '?z]]))

(deftest no-infinite-loops
  (are [x y sub] (c/unify x y sub)
    ['seq-of '?e] '?b+ [{'?b+ ['cat ['seq-of '?d]],
                         '?e ['or ['?b+ '?c]],
                         '?d ['or
                              [['seq-of '?g]
                               ['seq-of '?e]
                               ['cat ['or [#'clojure.core/seqable? ['seq-of '?h+]]]]]]}]))

(deftest perm-cache-works
  (c/unify #'int? #'string?)
  (is (seq @c/perm-cache)))
