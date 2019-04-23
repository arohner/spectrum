(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as spec-test]
            [spectrum.conform :as c]
            [spectrum.flow :as f]
            [spectrum.types :as t])
  (:import [clojure.lang IChunk]))

(deftest infer-var
  (are [v] (boolean (do
                      (println "infer-var" v)
                      (f/infer-var v {:dependencies? true})))
    #'apply
    #'clojure.core/reduce1
    #'clojure.core/spread
    #'list*
    #'str
    #'map
    #'true?
    ))

(deftest branch-prediction
  (are [f ret] (c/valid? ret (f/infer-form f))
    '(fn [s] (if (chunked-seq? s) (chunk-first s))) ['fn
                                                     {['cat '?x] ['or [#'nil? ['chunk '?y]]]}]))
