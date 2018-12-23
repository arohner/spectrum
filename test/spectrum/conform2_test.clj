(ns spectrum.conform2-test
  (:require [clojure.test :refer :all]
            [spectrum.conform2 :as c]
            [spectrum.unify :as u]))

(def a?)
(def b?)
(def c?)

(deftest valid-truthy
  (are [x y] (= true (c/valid? x y))
    #'any? #'a?
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
    (c/or #'a?) #'a?
    (c/or #'a? #'b?) #'a?
    (c/or #'a? #'b?) (c/or #'a? #'b?)
    (c/or #'a? '?x) #'a?
    (c/or #'a? '?x) '?x

    ;; cat
    (c/cat []) (c/cat [])
    (c/cat [#'a?]) (c/cat [#'a?])
    (c/cat [#'a? #'a?]) (c/cat [#'a? #'a?])
    (c/seq-of #'a?) (c/cat [#'a? #'a?])

    ;; ?
    (c/cat [(c/? #'b?)]) (c/cat [#'b?])
    (c/cat [#'a? (c/? #'b?) #'a?]) (c/cat [#'a? #'a?])
    (c/cat [#'a? (c/? #'b?) #'a?]) (c/cat [#'a? #'b? #'a?])

    ;; seq-of
    (c/seq-of #'a?) (c/cat [])
    (c/seq-of #'a?) (c/cat [#'a?])
    (c/seq-of #'a?) (c/cat [#'a? #'a?])

    (c/cat [(c/seq-of #'a?) #'b?]) (c/cat [#'b?])
    (c/cat [(c/seq-of #'a?) #'b?]) (c/cat [#'a? #'b?])
    (c/cat [(c/seq-of #'a?) #'b?]) (c/cat [#'a? #'a? #'b?])))

(deftest valid-falsey
  (are [x y] (= false (c/valid? x y))
    #'a? #'b?
    (c/vector-of '?x) (c/seq-of '?x)
    (c/coll-of #'a?) (c/vector-of #'b?)
    #'a? (c/or #'a? #'b?)

    ;; or
    (c/or #'a? #'b?) #'c?
    ;; cat
    (c/cat [#'b?]) (c/cat [#'a?])
    (c/cat [#'b?]) (c/cat [#'b? #'b?])
    (c/cat [#'a? #'a?]) (c/seq-of #'a?)
    ;; ?

    ;; seq
    (c/seq-of #'b?) (c/cat [#'a?])

    (c/cat [(c/seq-of #'a?) #'b?]) (c/cat [#'a? #'a?])))
