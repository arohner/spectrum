(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer (defspec)]
            [clojure.spec :as s]
            [clojure.spec.gen :as spec-gen]
            [clojure.spec.test]
            [spectrum.ann :as ann]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]
            [spectrum.flow-test :as flow-test])
  (:import (spectrum.conform Unknown
                             PredSpec
                             ClassSpec
                             AndSpec
                             OrSpec)))

(clojure.spec.test/instrument)

(deftest instance?-transformer
  (is (-> (c/maybe-transform #'instance? (c/cat- [(c/class-spec String) (c/parse-spec #'string?)])) :ret :v))

  (is (-> (c/maybe-transform #'instance? (c/cat- [(c/class-spec String) (c/unknown nil)])) :ret (= (c/parse-spec #'boolean?)))))

(defn transform-identical [args]
  (c/maybe-transform-method (flow/get-method! clojure.lang.Util 'identical (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
                            (flow/get-java-method-spec clojure.lang.Util 'identical args flow-test/dummy-analysis)
                            args))

(deftest identical
  (testing "true"
    (are [args] (= true (:ret (transform-identical args)))
      (c/cat- [1 1])
      (c/cat- [(c/pred-spec #'nil?) nil])
      (c/cat- [(c/pred-spec #'nil?) (c/pred-spec #'nil?)])
      (c/cat- [(c/pred-spec #'false?) false])))
  (testing "false"
    (are [args] (= false (:ret (transform-identical args)))
      (c/cat- [1 0])
      (c/cat- [(c/pred-spec #'nil?) 3])
      (c/cat- [(c/pred-spec #'integer?) nil])))
  (testing "unknown"
    (are [args] (= (c/class-spec Boolean) (:ret (transform-identical args)))
      (c/cat- [(c/pred-spec #'nil?) (c/or- [(c/pred-spec #'nil?) (c/unknown nil)])])
      (c/cat- [(c/pred-spec #'false?) (c/class-spec Boolean)])
      (c/cat- [(c/pred-spec #'boolean?) (c/pred-spec #'boolean?)])
      (c/cat- [(c/pred-spec #'boolean?) true]))))

(deftest empty-seq
  (testing "true"
    (are [arg] (= true (ann/empty-seq? arg))
      []
      nil
      (c/pred-spec #'nil?)))
  (testing "false"
    (are [arg] (= false (ann/empty-seq? arg))
      (c/coll-of (c/pred-spec #'keyword?)))))

(deftest map-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'identity) nil]) []
      (c/cat- [(c/get-var-fn-spec #'identity) (c/pred-spec #'nil?)]) []
      (c/cat- [(c/get-var-fn-spec #'identity) (c/coll-of (c/pred-spec #'keyword?))]) (c/coll-of (c/pred-spec #'keyword?))

      (c/cat- [(c/get-var-fn-spec #'vector) [1 :foo]]) (c/coll-of (c/pred-spec #'vector?))
      ))

  (testing "fail"
    (are [args] (= c/reject (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'inc) [:foo]])
      (c/cat- [(c/get-var-fn-spec #'inc) (c/coll-of (c/pred-spec #'keyword?))])
      )))

(deftest filter-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'filter args)))
      (c/cat- [(c/get-var-fn-spec #'identity) nil]) []
      (c/cat- [(c/get-var-fn-spec #'even?) (c/coll-of (c/pred-spec #'integer?))]) (c/coll-of (c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)] )))))

(deftest nil?-works
  (testing "true"
    (are [args] (= true (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [nil])))
  (testing "false"
    (are [args] (= false (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [false])
      (c/cat- [71])
      (c/cat- [(c/coll-of (c/pred-spec #'integer?))])))
  (testing "ambigous"
    (are [args] (= (c/pred-spec #'boolean?) (:ret (c/maybe-transform #'nil? args)))
      (c/cat- [(c/pred-spec #'boolean?)]))))
