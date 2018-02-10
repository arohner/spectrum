(ns spectrum.gen
  "Useful stuff for generative testing"
  (:require [clojure.spec.alpha :as s]
            [clojure.test.check.generators :as gen]
            clojure.spec.gen.alpha))

;; doesn't need to be complete, just long enough to be interesting
(def core-predicates #{#'any?
                       #'some?
                       #'number?
                       #'integer?
                       #'int?
                       #'pos-int?
                       #'neg-int?
                       #'nat-int?
                       #'float?
                       #'double?
                       #'boolean?
                       #'string?
                       #'ident?
                       #'simple-ident?
                       #'qualified-ident?
                       #'keyword?
                       #'simple-keyword?
                       #'qualified-keyword?
                       #'symbol?
                       #'simple-symbol?
                       #'qualified-symbol?
                       #'uuid?
                       #'uri?
                       #'inst?
                       #'seqable?
                       #'indexed?
                       #'map?
                       #'vector?
                       #'list?
                       #'seq?
                       #'char?
                       #'set?
                       #'nil?
                       #'false?
                       #'true?
                       #'zero?
                       #'rational?
                       #'coll?
                       #'empty?
                       #'associative?
                       #'sequential?
                       #'ratio?
                       #'bytes?})

(def core-predicates-gen (gen/elements core-predicates))
