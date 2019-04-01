(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [spectrum.ann :as ann]
            [spectrum.conform :as c]
            [spectrum.flow :as f]
            [spectrum.types :as t])
  (:import [clojure.lang IChunkedSeq ISeq]
           [java.util Map]))

(def a?)
(def b?)

(deftest canonicalize
  (are [t ret] (= ret (t/canonicalize t))
    #'true? (t/value-t true)
    #'zero? (t/value-t 0)
    (t/class-t String) #'string?
    #'string? #'string?
    (t/value-t nil) (t/value-t nil)
    #'int? #'int?
    (t/coll-of (var a?)) (t/coll-of (var a?))))

(deftest class-cast
  (are [t ret] (= ret (t/class-cast t))
    (t/seq-of a?) nil
    #'int? (t/or-t #{(t/class-t Byte) (t/class-t Long) (t/class-t Integer) (t/class-t Short)})
    #'chunked-seq? (t/class-t IChunkedSeq)
    #'seqable? (t/or-t (map t/class-t [clojure.lang.ISeq clojure.lang.Seqable Iterable CharSequence java.util.Map]))))

(deftest types
  (are [a b] (c/valid? a b)

    #'any? #'integer?
    #'integer? #'int?
    #'number? #'even?
    (t/value-t nil) #'nil?
    #'nil? (t/value-t nil)
    (t/value-t true) #'true?
    #'int? (t/value-t 1)

    (t/seq-of '?x) (t/seq-of '?x)
    (t/seq-of '?z) (t/seq-of '?z)
    #'seqable? (t/seq-of '?x)
    (t/coll-of '?x) (t/vector-of '?x)
    (t/coll-of #'a?) (t/vector-of #'a?)

    #'seqable? #'seq?
    #'seqable? (t/class-t ISeq)
    (t/class-t ISeq) (t/seq-of '?x)
    (t/class-t IChunkedSeq) #'chunked-seq?
    #'chunked-seq? (t/class-t IChunkedSeq)

    #'float? (t/class-t Double)
    #'float? (t/class-t Float)
    #'double? (t/class-t Double)
    (t/class-t Double) #'double?

    (t/class-t ISeq) (t/class-t IChunkedSeq)

    (t/and-t [#'int? #'any?]) #'int?

    (t/or-t [#'int? (t/class-t String)]) #'int?
    (t/or-t [(t/class-t Byte) (t/class-t Long) (t/class-t Integer) (t/class-t Short) (t/class-t String)]) #'int?

    ;; spec
    (t/cat-t [(t/seq-of #'int?)]) (t/cat-t [(t/value-t 1)])
    (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/value-t [[3]])
    (t/cat-t [(t/spec-t (t/cat-t [#'int?])) #'string?]) (t/value-t [[3] "foo"])
    ;; fn
    ['class clojure.lang.IFn] ['fn {['?t2] '?t3}]
    #'fn? ['fn {['?t2] '?t3}]
    #'ifn? ['fn {['?t2] '?t3}]
    #'ifn? #'fn?
    )

  (testing "invalid"
    (are [a b] (not (c/valid? a b))

      #'int? ['class Map]

      (t/seq-of '?x) (t/class-t IChunkedSeq)

      ;;spec

      (t/cat-t [#'int? #'string?]) [3 "foo"] ;; missing value-t
      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/value-t 1)
      (t/cat-t [(t/spec-t (t/seq-of '?x))]) (t/cat-t [(t/value-t 1)])

      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/value-t [[]])
      (t/cat-t [(t/spec-t (t/cat-t [#'int?]))]) (t/value-t [[1 2]])

      (t/cat-t [(t/seq-of #'int?)]) (t/value-t :foo)
      (t/cat-t [(t/seq-of (t/not-t #'int?))]) (t/value-t 1)

      ;; fn
      ['fn {['?t2] '?t3}] ['class clojure.lang.IFn]
      ['fn {['?t2] '?t3}] #'fn?
      ['fn {['?t2] '?t3}] #'ifn?
      )))

(deftest integration-tests
  (testing "truthy"
    (are [form] (do
                  (println "infer-form" form)
                  (boolean (f/infer-form form)))
      '(fn [x] (seq x))
      '(fn [x] (seq (seq x)))
      '(fn [x] (first x))
      '(fn [x] (first (seq x)))
      '(fn [x] (rest (seq x)))
      '(fn [x] (next (seq x)))))
  (testing "falsey"
    (are [form] (do
                  (println "infer-form" form)
                  (not (boolean (f/infer-form form))))

      '(first 1)
      '(rest 2)))

  (testing "return value"
    (are [form ret] (do
                      (println "infer-form" form)
                      (= ret (f/infer-form form)))
      '(list 1) ['and [#'list? ['cat ['value 1]]]]
      '(list 1 :a) ['and [#'list? ['cat ['value 1] ['value :a]]]]

      '(first 3) nil
      '(keyword 3) ['value nil]
      '(keyword "foo") #'simple-keyword?
      '(keyword "foo" "bar") #'qualified-keyword?

      '(fn [x] (keyword x)) ['fn
                             {['cat
                               ['or
                                [#'clojure.core/keyword?
                                 #'clojure.core/string?
                                 #'clojure.core/symbol?
                                 ['not
                                  ['or
                                   [#'clojure.core/keyword?
                                    #'clojure.core/string?
                                    #'clojure.core/symbol?]]]]]]
                              ['or [#'clojure.core/simple-keyword? ['value nil]]]}]

      '(fn [x y] (keyword x y)) ['fn {['cat #'string? #'string?] #'clojure.core/qualified-keyword?}]

      ;; apply
      '(apply keyword "foo") nil
      '(apply keyword ["foo"]) #'simple-keyword?
      '(apply keyword ["foo" "bar"]) #'qualified-keyword?
      '(apply keyword "foo" "bar") nil
      '(apply keyword "foo" ["bar"]) #'qualified-keyword?
      '(apply keyword "foo" "bar" []) #'qualified-keyword?

      '(apply true? [1]) ['or [['value true] ['value false] ['class Boolean/TYPE]]]
      '(apply true? 1) nil
      ))

  (testing "args"
    (are [form args ret] (c/unify ret (f/infer-form form args))
      '(first x) {:x ['seq-of #'int?]} ['or #{#'int? #'nil?}]
      '(cons x y) {:x '?x :y (t/seq-of '?y)} ['cat '?x (t/seq-of '?y)]
      ))

  (testing "TBD"
    (comment
      (are [form ret] (= ret (f/infer-form form))
        '(inc "foo") nil
        '(= 1 2) ['value false]
        '(= 3 3) ['value true]

        '(list 1 :a :b "foo") '[and [cat [seq-of [or #'int? #'keyword? #'string?]]] #'list?])?)))
