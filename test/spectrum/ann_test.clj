(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [spectrum.ann :as ann]
            [spectrum.types :as t]
            [spectrum.conform :as c])
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
    (t/or-t [(t/class-t Byte) (t/class-t Long) (t/class-t Integer) (t/class-t Short) (t/class-t String)]) #'int?)

  (testing "invalid"
    (are [a b] (not (c/valid? a b))
      (t/seq-of '?x) (t/class-t IChunkedSeq))))

(deftest apply-invoke-ann
  (testing "truthy"
    (are [v args ret] (c/valid? (t/or-t [#'int? #'nil?]) (t/invoke-t v (t/cat-t args)))
      #'first [(t/seq-of #'int?)] [(t/or-t [#'int? #'nil?])]
      ;; #'first [#'seqable?] [(t/or-t ['?x #'nil?])]
      )))
