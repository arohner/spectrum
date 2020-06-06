(ns spectrum.repl
  (:require [clojure.math.combinatorics :as combo]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.test.check.generators :as gen]
            [spectrum.compiler :as c]
            [spectrum.compiler-test :as ct]
            [spectrum.data :as data]
            [spectrum.equations :as eq]
            [spectrum.flow :as f]
            [spectrum.types :as t]
            [spectrum.flow-test :as ft]
            [spectrum.ann-test :as at]))

;; (c/load-data-readers)
;; (s/check-asserts true)

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
