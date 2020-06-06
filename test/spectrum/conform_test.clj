(ns spectrum.conform-test
  (:require [clojure.test :refer :all]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.clojure-test :refer [defspec]]
            [spectrum.conform :as c]
            [spectrum.types :as t])
  (:import [clojure.lang Keyword LazySeq]))

(def a?)
(def b?)
(def c?)

(deftest occurs?
  (testing "truthy"
    (are [x y subst] (= true (c/occurs? x y subst))
      '?x (t/seq-of '?x) {}
      '?x '?y {'?y '?x}
      ))
  (testing "falsey"
    (are [x y subst] (not (c/occurs? x y subst))
      '?x '?y {}
      '?t1 (t/or-t #{'?k #'char?}) {'?k '?x, '?x (t/or-t #{'?k #'char?})}
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
      (t/or-t ['?a '?b]) '?x [{'?x '?a} {'?x '?b}]
      (t/or-t [#'int?]) '?x [{'?x #'int?}]

      (t/or-t ['?a '?b]) #'int? [{'?a (t/or-t [#'int? '?a])
                                  '?b (t/or-t [#'int? '?b])}]

      (t/or-t ['?a '?b]) (t/or-t [#'int? #'string?]) [{'?a (t/or-t [#'clojure.core/int? #'clojure.core/string? '?a])
                                                       '?b (t/or-t [#'clojure.core/int? #'clojure.core/string? '?b])}]

      (t/or-t ['?x '?y '?z]) (t/or-t ['?a '?b]) [{'?a (t/or-t '[?a ?x ?y ?z])
                                                  '?b (t/or-t '[?b ?x ?y ?z])}]

      (t/or-t [(t/vector-of '?x) (t/coll-of '?x)]) '?t1 [{'?t1 (t/or-t [(t/vector-of '?x) (t/coll-of '?x)])}]
      (t/or-t [(t/spec-t (t/vector-of '?x)) (t/coll-of '?x)]) '?t1 [{'?t1 (t/or-t [(t/spec-t (t/vector-of '?x)) (t/coll-of '?x)])}]


      ;; cat
      (t/cat-t [(t/? '?a)]) (t/cat-t [(t/? #'int?)]) [{'?a (t/or-t [#'int? '?a nil])}]

      (t/cat-t [(t/seq-of '?a)]) (t/cat-t [(t/seq-of #'int?)]) [{'?a (t/or-t [#'int? '?a])}]

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

      (t/seq-of '?x) (t/seq-of '?y) [{'?x #'string? '?y #'int?}] nil

      ;; fn
      (t/fn-t {['?a] '?b}) (t/fn-t {['?c] '?d ['?e '?f] '?g}) [{}] [{'?c '?a '?d '?b}]

      ;; recursive substs
      '?x (t/seq-of #'nil?) [{'?x (t/seq-of '?y) '?y (t/or-t #{'?x #'nil?})}] nil

      (t/seq-of '?x) (t/seq-of #'nil?) [{'?x '?y '?y (t/or-t #{#'nil? (t/seq-of '?x) #'seqable?})}] [{'?x '?y '?y (t/or-t #{#'nil? (t/seq-of '?x) #'seqable?})}]

      '?x #'b? [{'?x (t/seq-of '?y) '?y (t/or-t #{'?x #'nil?})}] nil
      '?x (t/seq-of #'b?) [{'?x (t/seq-of '?y) '?y (t/or-t #{'?x #'nil?})}] nil

      ))

  (testing "substs contains"
    (are [x y substs] (= substs (set/intersection substs (set (c/unify x y))))
      '?x (t/value-t :foo) #{{'?x (t/value-t :foo)}}))

  (testing "substs ="
    (are [x y substs] (= (set substs) (set (c/unify x y)))
      '?x (t/and-t #{'?y #'clojure.core/chunked-seq?}) [{'?x (t/and-t #{'?y #'chunked-seq?})}]
      (t/cat-t ['?a (t/cat-t ['?b])]) (t/cat-t '[?c ?d]) '[{?c ?a, ?d ?b}]
      '?x (t/value-t nil) [{'?x (t/value-t nil)}]))

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
    (are [t] (t/regex? t)
      (t/cat-t [])
      (t/cat-t [#'int?])
      (t/value-t [1 2 3])))
  (testing "falsey"
    (are [t] (= false (t/regex? t))
      #'int?
      (t/value-t 3))))

(deftest dx
  (are [x y ret] (= (set ret) (set (c/dx x y [{}])))
    (t/cat-t []) #'a? nil
    (t/cat-t [#'a?]) #'a? [{:state nil :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'a? [{:state (t/cat-t [(t/seq-of #'a?) #'b?]) :substs [{}]}
                                           {:state (t/cat-t [#'b?]) :substs [{}]}]
    (t/cat-t [(t/seq-of #'a?) #'b?]) #'b? [{:state nil :substs [{}]}]

    (t/seq-of (t/class-t Character)) (t/value-t \f) [{:state (t/seq-of (t/class-t Character)) :substs [{}]}
                                                     {:state nil :substs [{}]}]

    #'int? #'int? [{:state nil :substs [{}]}]
    (t/value-t 1) (t/value-t 1) [{:state nil :substs [{}]}]
    (t/cat-t [(t/value-t 1)]) (t/value-t 1) [{:state nil :substs [{}]}]
    ))

(deftest valid?
  (testing "truthy"
    (are [x y] (do
                 ;; (println "valid?" x y)
                 (= true (c/valid? x y)))
      '?x (t/value-t 3)
      nil nil
      #'any? #'a?
      #{:foo :bar} #{:foo :bar}
      {:a :b} {:a :b}
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
      (t/seq-of #'char?) (t/value-t "foo")

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
      (t/coll-of '?x) (t/spec-t (t/seq-of '?x))
      (t/coll-of '?x) (t/spec-t (t/seq-of '?y))
      #'seqable? (t/spec-t (t/seq-of '?y))

      (t/cat-t [(t/spec-t (t/seq-of '?x))]) (t/cat-t ['?y])
      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/cat-t [(t/spec-t (t/cat-t [#'int?]))])

      (t/cat-t [(t/spec-t (t/seq-of '?x))]) (t/cat-t [(t/value-t nil)])

      ;; '?a '[invoke ?x [cat ?y]]
      ))

  (testing "falsey"
    (are [x y] (do
                 (println "valid?" x y)
                 (= false (c/valid? x y)))
      1 2
      [1] [2]
      ['?x] [1 2]
      #{:foo} :bar
      :bar #{:foo}
      #'a? #'b?
      (t/vector-of '?x) (t/seq-of '?x)
      (t/coll-of #'a?) (t/vector-of #'b?)
      #'a? (t/or-t [#'a? #'b?])

      ;; or
      (t/or-t [#'a? #'b?]) #'c?
      ;; and
      (t/and-t [#'a? #'b? #'c?]) (t/and-t [#'a? #'b?])

      ;;not
      #'int? (t/not-t #'int?)
      #'int? (t/not-t #'string?)
      #'int? (t/not-t #'even?) ;; could be string
      #'int? (t/and-t [#'any? (t/not-t #'string?)])
      (t/and-t [#'a? #'b? #'c?]) (t/and-t [#'a? #'b?])
      (t/and-t [#'a? #'b? #'c?]) (t/and-t [#'a? #'b? (t/not-t #'c?)])

      ;; cat
      (t/cat-t [#'b?]) (t/cat-t [#'a?])
      (t/cat-t [#'b?]) (t/cat-t [#'b? #'b?])
      ;; ?

      ;; seq
      (t/seq-of #'a?) (t/seq-of #'b?)
      (t/seq-of #'b?) (t/cat-t [#'a?])
      (t/seq-of #'int?) #'int?
      (t/seq-of '?a) #'any?

      (t/cat-t [(t/seq-of #'a?) #'b?]) (t/cat-t [#'a? #'a?])

      (t/class-t Integer) (t/class-t Keyword)

      ;; value
      #'string? (t/value-t 3)
      #'associative? (t/value-t false)

      (t/value-t nil) (t/seq-of Character)
      (t/value-t 3) 3
      (t/value-t nil) nil

      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/cat-t [#'int?])
      )))

(deftest and-logic
  (are [ts ret] (= ret (t/and-t ts))
    ['?x] '?x
    ['?x '?y] (t/and-t ['?x '?y])
    [#'any?] #'any?

    ;; (t/and-t [#'a? (t/or-t [#'a? #'b?])]) #'a?
    ;; (t/and-t [#'int? (t/or-t [#'even? #'odd?])]) #'a?
    ))

(deftest or-logic
  (are [ts ret] (= ret (t/or-t ts))
    ['?x] '?x
    ['?x '?y] (t/or-t ['?x '?y])
    ['?x (t/or-t ['?y '?z])] (t/or-t ['?x '?y '?z])))

(deftest handles-free-cycles
  (are [x y sub] (c/unify x y sub)
    '?x1 '?y1 [{'?y1 '?y2,
                '?y2 (t/and-t ['?y3 (t/class-t clojure.lang.LazySeq)]),
                '?y3 '?y4,
                '?x1 (t/seq-of '?x2)}]

    '?x1 '?y1 [{'?y1 '?y2,
                '?y2 (t/and-t ['?y3 (t/class-t clojure.lang.LazySeq)]),
                '?y3 '?y4,
                '?y4 '?y5,
                '?y5 '?y4,
                '?x1 (t/seq-of '?x2)}]))

(deftest cyclic-substs
  (is (c/unify '?x1 '?y1 [{'?y1 '?y2,
                           '?y2 (t/and-t ['?y3 (t/class-t clojure.lang.LazySeq)]),
                           '?y3 '?y4,
                           '?x1 (t/seq-of '?x2)}]))
  (is (c/unify '?x1 '?y1 [{'?y1 '?y2,
                           '?y2 (t/and-t ['?y3 (t/class-t clojure.lang.LazySeq)]),
                           '?y3 '?y4,
                           '?y4 '?y5,
                           '?y5 '?y4,
                           '?x1 (t/seq-of '?x2)}])))

(deftest perm-cache-works
  (c/unify #'int? #'string?)
  (is (seq @c/perm-cache)))

(defspec or-left 500
  (prop/for-all [a (s/gen (s/spec ::t/type))
                 b (s/gen (s/spec ::t/type))
                 c (s/gen (s/spec ::t/type))]
    (if (c/unify a b)
      (c/unify (t/or-t [a c]) b)
      true)))

(defspec or-right-positive 500
  (prop/for-all [a (s/gen (s/spec ::t/type))
                 b (s/gen (s/spec ::t/type))
                 c (s/gen (s/spec ::t/type))]
    (if (and (c/unify a b) (c/unify a c))
      (and (c/unify a (t/or-t [b c]))
           (c/unify a (t/or-t [c b])))
      true)))

(defspec or-right-negative 500
  (prop/for-all [a (s/gen (s/spec ::t/type))
                 b (s/gen (s/spec ::t/type))
                 c (s/gen (s/spec ::t/type))]
    (if (and (c/unify a b) (not (c/unify a c)))
      (not (c/unify a (t/or-t [b c])))
      true)))

(defspec and-right 500
  (prop/for-all [a (s/gen (s/spec ::t/type))
                 b (s/gen (s/spec ::t/type))
                 c (s/gen (s/spec ::t/type))]
    (if (and (or (c/unify a b) (c/unify a c))
             (t/and-t? (t/and-t [b c])))
      (c/unify a (t/and-t [b c]))
      true)))

(def gen-type-spec-atoms
  (gen/elements
   [#'coll?
    #'keyword?
    #'map?
    #'number?
    #'ratio?
    #'seq?
    #'seqable?
    #'set?
    #'string?
    #'true?
    #'int?]))

(def gen-coll-of (gen/fmap (fn [t]
                             (t/coll-of t)) gen-type-spec-atoms))

(def gen-seq-of (gen/fmap (fn [t]
                            (t/seq-of t)) gen-type-spec-atoms))

(def gen-map-of (gen/fmap (fn [[k v]]
                            (t/map-of k v)) (gen/vector gen-type-spec-atoms 2)))

(def gen-cat-t (gen/fmap (fn [ts]
                           (t/cat-t ts)) (gen/vector gen-type-spec-atoms)))

(def gen-type-specs (gen/one-of [gen-type-spec-atoms
                                 gen-coll-of
                                 gen-map-of
                                 gen-seq-of
                                 gen-cat-t]))

(defspec types-match-specs 100
  (prop/for-all [a gen-type-specs
                 b gen-type-specs]
    (let [as (t/type-spec a)
          bs (t/type-spec b)
          bt (gen/generate (s/gen bs))
          s-valid? (s/valid? as bt)
          unified? (boolean (c/unify a b))]
      (= s-valid? unified?))))
