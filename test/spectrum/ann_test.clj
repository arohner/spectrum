(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer (defspec)]
            [clojure.spec :as s]
            [clojure.spec.gen :as spec-gen]
            [clojure.spec.test]
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
    (are [args] (= (c/value true) (:ret (transform-identical args)))
      (c/cat- [(c/value 1) (c/value 1)])
      (c/cat- [(c/pred-spec #'nil?) (c/value nil)])
      (c/cat- [(c/pred-spec #'nil?) (c/pred-spec #'nil?)])
      (c/cat- [(c/pred-spec #'false?) (c/value false)])))
  (testing "false"
    (are [args] (= c/reject (:ret (transform-identical args)))
      (c/cat- [(c/value 1) (c/value 0)])
      (c/cat- [(c/pred-spec #'nil?) (c/value 3)])
      (c/cat- [(c/pred-spec #'integer?) (c/value nil)])))
  (testing "unknown"
    (are [args] (= (c/class-spec Boolean) (:ret (transform-identical args)))
      (c/cat- [(c/pred-spec #'nil?) (c/or- [(c/pred-spec #'nil?) (c/unknown nil)])])
      (c/cat- [(c/pred-spec #'false?) (c/class-spec Boolean)])
      (c/cat- [(c/pred-spec #'boolean?) (c/pred-spec #'boolean?)])
      (c/cat- [(c/pred-spec #'boolean?) (c/value true)]))))

(deftest map-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/pred-spec #'nil?)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/coll-of-spec (c/pred-spec #'keyword?))]) (c/coll-of-spec (c/pred-spec #'keyword?))

      (c/cat- [(c/get-var-fn-spec #'vector) (c/value [(c/value 1) (c/value :foo)])]) (c/coll-of-spec (c/pred-spec #'vector?))
      ))

  (testing "fail"
    (are [args] (= c/reject (:ret (c/maybe-transform #'map args)))
      (c/cat- [(c/get-var-fn-spec #'inc) (c/value [(c/value :foo)])])
      (c/cat- [(c/get-var-fn-spec #'inc) (c/coll-of-spec (c/pred-spec #'keyword?))])
      )))

(deftest filter-tests
  (testing "equals"
    (are [args expected] (= expected (:ret (c/maybe-transform #'filter args)))
      (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'even?) (c/coll-of (c/pred-spec #'integer?))]) (c/coll-of (c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)] )))))
