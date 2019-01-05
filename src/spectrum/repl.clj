(ns spectrum.repl
  (:require [clojure.math.combinatorics :as combo]
            [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.test.check.generators :as gen]
            ;; [spectrum.check :as check]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as f]
            [spectrum.types :as t]))

;; (c/load-data-readers)
;; (s/check-asserts true)

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
