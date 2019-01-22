(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as spec-test]
            [spectrum.conform :as c]
            [spectrum.flow :as f]))

(deftest infer-var
  (are [v] (boolean (f/infer-var v {:dependencies? true}))
    #'str
    #'apply))
