(ns spectrum.repl
  (:require [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.test.check.generators :as gen]
            [spectrum.check :as check]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]))

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
