(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.flow :as flow]))

(s/fdef user/foo :args integer? :ret integer?)

(deftest basic
  (is (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x))))))

(deftest maybe-assoc-var-name-works
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr :spectrum.flow/var))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init :spectrum.flow/var)))

(deftest maybe-assoc-fn-specs
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr :spectrum.flow/spec))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init :spectrum.flow/spec)))
