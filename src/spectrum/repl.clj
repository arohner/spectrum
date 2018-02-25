(ns spectrum.repl
  (:require [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.test.check.generators :as gen]
            [spectrum.check :as check]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]))

(defn infer-var
  "infer a var return the spec"
  [v]
  (-> v .ns str symbol check/ensure-analysis)
  (-> v
      (data/get-var-analysis)
      (flow/flow)
      :init
      flow/maybe-strip-meta
      ::flow/ret-spec))

(in-ns 'clojure.core)

(defmacro inspect [expr]
  `(do
     (let [in# (quote ~expr)
         resp# (do ~expr)]
       (printf "%s is %s\n" in# (with-out-str (print resp#)))
       resp#)))
