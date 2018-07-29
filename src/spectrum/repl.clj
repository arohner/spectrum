(ns spectrum.repl
  (:require [clojure.math.combinatorics :as combo]
            [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.test.check.generators :as gen]
            [spectrum.protocols :as p]
            [spectrum.check :as check]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]))

(defn infer-var
  "infer a var return the spec"
  [^clojure.lang.Var v]
  (-> v .ns str symbol check/ensure-analysis)
  (assert (data/get-var-analysis v))
  (-> v
      (data/get-var-analysis)
      (flow/infer)
      :init
      flow/maybe-strip-meta
      ::flow/ret-spec))

(c/load-data-readers)
(s/check-asserts true)

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
