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
  (are [v] (boolean (f/infer-var v {:dependencies? true}))
    #'str
    #'apply
    #'clojure.core/spread
    #'clojure.core/reduce1))

(deftest branch-prediction
  (are [f ret] (= ret (f/infer-form f))
    '(fn [s] (if (chunked-seq? s) (chunk-first s))) (t/fn-t {[#'any?] (t/or-t [['class IChunk] #'nil?])})))
