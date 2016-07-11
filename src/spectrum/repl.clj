(ns spectrum.repl
  (:require [clojure.spec :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.check :as st]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]))

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
