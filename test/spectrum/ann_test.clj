(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [spectrum.ann :as ann]
            [spectrum.conform :as c]
            [spectrum.flow :as f]
            [spectrum.types :as t])
  (:import [clojure.lang IChunkedSeq ISeq]))

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

    (t/seq-of '?x) (t/seq-of '?x)
    (t/seq-of '?z) (t/seq-of '?z)
    #'seqable? (t/seq-of '?x)
    (t/coll-of '?x) (t/vector-of '?x)
    (t/coll-of #'a?) (t/vector-of #'a?)

    (t/class-t ISeq) (t/seq-of '?x)
    (t/class-t IChunkedSeq) #'chunked-seq?
    #'chunked-seq? (t/class-t IChunkedSeq)

    (t/class-t ISeq) (t/class-t IChunkedSeq)

    (t/and-t [#'int? #'any?]) #'int?
    (t/or-t [(t/class-t Byte) (t/class-t Long) (t/class-t Integer) (t/class-t Short) (t/class-t String)]) #'int?


    ;; fn
      ['class clojure.lang.IFn] ['fn {['?t2] '?t3}])

  (testing "invalid"
    (are [a b] (not (c/valid? a b))
      (t/seq-of '?x) (t/class-t IChunkedSeq))))

(deftest integration-tests
  (testing "truthy"
    (are [form] (boolean (f/infer-form form))
      '(fn [x] (seq x))
      '(fn [x] (seq (seq x)))
      '(fn [x] (first x))
      '(fn [x] (first (seq x)))
      '(fn [x] (rest (seq x)))
      '(fn [x] (next (seq x)))))
  (testing "falsey"
    (are [form] (not (boolean (f/infer-form form)))

      '(keyword 3)
      '(first 1)
      '(rest 2)))
  (testing "return value"
    (are [form ret] (= ret (f/infer-form form))
      '(keyword "foo" "bar") #'qualified-keyword?
      ))

  ;; (testing "args"
  ;;   (are [form args ret] (= ret (f/infer-form form args))

  ;;     ))

  (testing "TBD"
    (comment
      (are [form ret] (= ret (f/infer-form form))
        '(inc "foo") nil
        '(= 1 2) ['value false]
        '(= 3 3) ['value true]

        '(first x) {:x ['seq-of #'int?]} ['or #{#'int? #'nil?}]
        '(cons x y) {:x '?x :y (t/seq-of '?y)} ['cat '?x (t/seq-of '?y)]

        '(keyword "foo") #'simple-keyword?

        ;; apply
      '(apply keyword "foo") nil
      '(apply keyword ["foo"]) #'simple-keyword?
      '(apply keyword "foo" "bar") nil
      '(apply keyword ["foo" "bar"]) #'qualified-keyword?
      '(apply keyword "foo" ["bar"]) #'qualified-keyword)?)))
