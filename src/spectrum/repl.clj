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

            ))

;; (c/load-data-readers)
;; (s/check-asserts true)

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
