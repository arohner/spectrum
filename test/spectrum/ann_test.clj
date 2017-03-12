(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer (defspec)]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [clojure.spec.gen :as spec-gen]
            [clojure.spec.test]
            [spectrum.ann :as ann]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.check :as check]
            [spectrum.flow :as flow]
            [spectrum.flow-test :as flow-test])
  (:import (spectrum.conform Unknown
                             PredSpec
                             ClassSpec
                             AndSpec
                             OrSpec)))

(clojure.spec.test/instrument)

(check/ensure-analysis 'spectrum.analyzer-spec)

(deftest instance?-transformer
  (is (-> (c/maybe-transform #'instance? (c/cat- [(c/class-spec String) (c/parse-spec #'string?)])) :ret :v))

  (is (-> (c/maybe-transform #'instance? (c/cat- [(c/class-spec String) (c/unknown nil)])) :ret (= (c/parse-spec #'boolean?)))))

(defn transform-identical [args]
  (c/maybe-transform-method (flow/get-method! clojure.lang.Util 'identical (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
                            (flow/get-java-method-spec clojure.lang.Util 'identical args flow-test/dummy-analysis)
                            args))

(deftest identical
  (testing "true"
    (are [args] (= (c/value true) (:ret (transform-identical args)))
      (c/cat- [(c/value 1) (c/value 1)])
      (c/cat- [(c/pred-spec #'nil?) (c/value nil)])
      (c/cat- [(c/pred-spec #'nil?) (c/pred-spec #'nil?)])
      (c/cat- [(c/pred-spec #'false?) (c/value false)])))
  (testing "false"
    (are [args] (= (c/value false) (:ret (transform-identical args)))
      (c/cat- [(c/value 1) (c/value 0)])
      (c/cat- [(c/pred-spec #'nil?) (c/value 3)])
      (c/cat- [(c/pred-spec #'integer?) (c/value nil)])))
  (testing "unknown"
    (are [args] (= (c/class-spec Boolean) (:ret (transform-identical args)))
      (c/cat- [(c/pred-spec #'nil?) (c/or- [(c/pred-spec #'nil?) (c/unknown nil)])])
      (c/cat- [(c/pred-spec #'false?) (c/class-spec Boolean)])
      (c/cat- [(c/pred-spec #'boolean?) (c/pred-spec #'boolean?)])
      (c/cat- [(c/pred-spec #'boolean?) (c/value true)]))))

(deftest empty-seq
  (testing "true"
    (are [arg] (= true (ann/empty-seq? arg))
      (c/value [])
      (c/value nil)
      (c/pred-spec #'nil?)))
  (testing "false"
    (are [arg] (= false (ann/empty-seq? arg))
      (c/coll-of (c/pred-spec #'keyword?)))))

(deftest map-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/pred-spec #'nil?)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/coll-of (c/pred-spec #'keyword?))]) (c/coll-of (c/pred-spec #'keyword?))

      (c/cat- [(c/get-var-fn-spec #'vector) (c/value [(c/value 1) (c/value :foo)])]) (c/coll-of (c/pred-spec #'vector?))
      ))

  (testing "fail"
    (are [args] (= c/reject (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'inc) (c/value [(c/value :foo)])])
      (c/cat- [(c/get-var-fn-spec #'inc) (c/coll-of (c/pred-spec #'keyword?))])
      )))

(deftest filter-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'filter args)))
      (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'even?) (c/coll-of (c/pred-spec #'integer?))]) (c/coll-of (c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)] )))))

(deftest nil?-works
  (testing "true"
    (are [args] (= (c/value true) (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [(c/value nil)])))
  (testing "false"
    (are [args] (= (c/value false) (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [(c/value false)])
      (c/cat- [(c/value 71)])
      (c/cat- [(c/coll-of (c/pred-spec #'integer?))])))
  (testing "ambigous"
    (are [args] (= (c/pred-spec #'boolean?) (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [(c/pred-spec #'boolean?)]))))

(deftest inc-works
  (testing "true"
    (are [args ret] (= ret (:ret (c/maybe-transform #'inc args)))
      (c/cat- [(c/pred-spec #'integer?)]) (c/class-spec Long)
      (c/cat- [(c/pred-spec #'float?)]) (c/class-spec Double)
      (c/cat- [(c/value 3)]) (c/class-spec Long)
      (c/cat- [(c/pred-spec #'string?)]) c/reject)))

(deftest conform-ann
  ;; conform tests that require ann.clj or core_specs.clj to work
  (are [spec val] (= val (c/conform spec val))
    (c/pred-spec #'number?) (c/pred-spec #'integer?)
    (c/pred-spec #'map?) (c/keys-spec {} {} {} {})
    (c/parse-spec ::ana.jvm/analysis) (c/parse-spec ::flow/analysis)
    (c/parse-spec ::ana.jvm/analysis) (c/parse-spec ::ana.jvm/analysis)
    (c/pred-spec #'c/spect?) (c/value false)))
