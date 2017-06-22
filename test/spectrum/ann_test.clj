(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer (defspec)]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as spec-gen]
            [clojure.spec.test.alpha]
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
                             OrSpec)
           [clojure.lang BigInt PersistentHashMap Ratio Seqable]))

(clojure.spec.test.alpha/instrument)

(check/ensure-analysis 'spectrum.analyzer-spec)

(deftest instance?-transformer
  (are [c x expected] (= expected (c/invoke (c/get-var-fn-spec #'instance?) (c/cat- [c x])))
    (c/class-spec String) (c/pred-spec #'string?) (c/value true)
    (c/class-spec String) (c/class-spec String) (c/value true)
    (c/class-spec String) (c/pred-spec #'integer?) (c/value false)
    (c/class-spec String) (c/unknown {:message ""}) (c/pred-spec #'boolean?)))


(defn transform-identical [args]
  (c/maybe-transform-method (flow/get-method! clojure.lang.Util 'identical (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
                            (flow/get-java-method-spec clojure.lang.Util 'identical args)
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
    (are [args] (= (c/class-spec Boolean/TYPE) (:ret (transform-identical args)))
      (c/cat- [(c/pred-spec #'nil?) (c/or- [(c/pred-spec #'nil?) (c/unknown {:message ""})])])
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
  (testing "successful"
    (are [args expected] (= expected (c/invoke (c/get-var-fn-spec #'map) args))
      (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/pred-spec #'nil?)]) (c/value [])
      (c/cat- [(c/get-var-fn-spec #'identity) (c/coll-of (c/pred-spec #'keyword?))]) (c/coll-of (c/pred-spec #'keyword?))

      (c/cat- [(c/get-var-fn-spec #'vector) (c/value [(c/value 1) (c/value :foo)])]) (c/coll-of (c/pred-spec #'vector?))))

  (testing "fail"
    (are [args] (c/invalid? (c/invoke (c/get-var-fn-spec #'map) args))
      (c/cat- [(c/get-var-fn-spec #'inc) (c/value [(c/value :foo)])])
      (c/cat- [(c/get-var-fn-spec #'inc) (c/coll-of (c/pred-spec #'keyword?))]))))

(deftest nil?-works
  (testing "true"
    (are [arg] (= (c/value true) (check/type-of '(nil? x) {:x arg}))
      (c/value nil)))
  (testing "false"
    (are [arg] (= (c/value false) (check/type-of '(nil? x) {:x arg}))
      (c/value false)
      (c/value 71)
      (c/coll-of (c/pred-spec #'integer?))))
  (testing "ambigous"
    (are [arg] (= (c/class-spec Boolean/TYPE) (check/type-of '(nil? x) {:x arg}))
      (c/pred-spec #'boolean?))))

(deftest inc-works
  (testing "true"
    (are [arg ret] (c/equivalent? ret (check/type-of '(inc x) {:x arg}))
      (c/pred-spec #'int?) (c/class-spec Long)
      (c/pred-spec #'integer?) (c/or- [(c/class-spec Long) (c/class-spec BigInt)])
      (c/pred-spec #'float?) (c/class-spec Double/TYPE)
      (c/value 3) (c/class-spec Long/TYPE)))

  ;; TODO technically not illegal because the java method takes Object. Need to override
  (testing "falsey"
    (are [arg ret] (c/invalid? (check/type-of '(inc x) {:x arg}))
      (c/pred-spec #'string?)
      (c/pred-spec #'nil?))))

(deftest conform-ann
  ;; conform tests that require ann.clj or core_specs.clj to work
  (testing "truthy"
    (are [spec val] (c/conformy? (c/conform spec val))
      (c/pred-spec #'int?) (c/class-spec Long)
      (c/pred-spec #'number?) (c/pred-spec #'integer?)
      (c/pred-spec #'map?) (c/keys-spec {} {} {} {})
      (c/parse-spec ::ana.jvm/analysis) (c/parse-spec ::flow/analysis)
      (c/parse-spec ::ana.jvm/analysis) (c/parse-spec ::ana.jvm/analysis)
      (c/coll-of ::ana.jvm/analysis) (c/coll-of ::flow/analysis)
      (c/pred-spec #'c/spect?) (c/value false)
      (c/pred-spec #'seqable?) (c/class-spec clojure.lang.PersistentHashMap)
      (c/pred-spec #'seqable?) (c/class-spec Seqable)
      (c/pred-spec #'seqable?) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))

      (c/or- [(c/pred-spec #'integer?) (c/pred-spec #'even?)]) (c/pred-spec #'even?)
      (c/or- [(c/class-spec Long) (c/class-spec Integer) (c/class-spec Short) (c/class-spec Byte)]) (c/pred-spec #'int?)

      (c/parse-spec :spectrum.core-specs/seq-like) (c/class-spec Seqable)))
  (testing "falsey"
    (are [spec val] (c/invalid? (c/conform spec val))
      (c/pred-spec #'float?) (c/value 3))))

(deftest invoke-ann
  (are [spec args expected] (= expected (c/invoke spec args))
    (c/pred-spec #'seqable?) (c/cat- [(c/keys-spec {} {} {} {})]) (c/value true)
    (c/pred-spec #'seqable?) (c/cat- [(c/class-spec Seqable)]) (c/value true)
    (c/pred-spec #'seq?) (c/cat- [(c/keys-spec {} {} {} {})]) (c/value false)
    (c/pred-spec #'integer?) (c/cat- [(c/pred-spec #'even?)]) (c/value true)
    (c/pred-spec #'integer?) (c/cat- [(c/value 3)]) (c/value true)
    (c/pred-spec #'integer?) (c/cat- [(c/class-spec Long)]) (c/value true)))

(deftest spec-class-ann
  (are [spec expected] (= expected (c/spec->classes spec))
    (c/class-spec Double/TYPE) #{Double/TYPE}
    (c/class-spec Long) #{Long}
    (c/pred-spec #'string?) #{String}
    (c/class-spec String) #{String}
    (c/pred-spec #'float?) #{Float Double}
    (c/pred-spec #'int?) #{Byte Short Integer Long}))

(deftest add
  (are [form args expected] (c/equivalent? expected (check/type-of form args))
    '(+ 1 1) {} (c/class-spec Long/TYPE)
    '(+ 1 x) {:x (c/pred-spec #'int?)} (c/class-spec Long/TYPE)

    '(+ 1 x) {:x (c/pred-spec #'integer?)} (c/or- [(c/class-spec Long) (c/class-spec BigInt)])

    '(+ 1.0 x) {:x (c/pred-spec #'int?)} (c/class-spec Double/TYPE)
    '(+ 1.0 x) {:x (c/class-spec BigInt)} (c/class-spec Double/TYPE)
    '(+ 1 2.0) {} (c/class-spec Double/TYPE)
    '(+ 22/7 1) {} (c/class-spec Ratio)
    '(+ 22/7 1.0) {} (c/class-spec Double/TYPE)
    '(+ 22/7 x) {:x (c/class-spec BigInt)} (c/class-spec Ratio)
    '(+ 1 x) {:x (c/class-spec BigDecimal)} (c/class-spec BigDecimal)
    '(+ 1.0 x) {:x (c/class-spec BigDecimal)} (c/class-spec Double/TYPE)
    '(+ 1/2 (bigdec 1)) {} (c/class-spec BigDecimal)
    '(+ x y) {:x (c/class-spec BigDecimal)
              :y (c/class-spec BigInt)} (c/class-spec BigDecimal)))

;; TODO

;; (deftest filter-tests
;;   (testing "equals"
;;     (are [args expected] (= expected (:ret (c/maybe-transform #'filter args)))
;;       (c/cat- [(c/get-var-fn-spec #'identity) (c/value nil)]) (c/value [])
;;       (c/cat- [(c/get-var-fn-spec #'even?) (c/coll-of (c/pred-spec #'integer?))]) (c/coll-of (c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)] )))))

;; (deftest filter-invoke
;;   ;; Checks that filter accepts or rejects arguments
;;   (testing "valid"
;;     (are [form env] (c/valid? #'any? (check/type-of form env))
;;       '(filter identity (range 5)) {}
;;       '(filter even? (range 5)) {}
;;       '(filter identity x) {:x (c/parse-spec (s/or :i integer? :n nil?))}
;;       '(filter even? x) {:x (c/parse-spec (s/or :i odd? :s even?))}
;;       '(filter :foo x) {:x (c/parse-spec (s/coll-of (s/or :foo (s/keys :req-un {:foo string?})
;;                                                           :bar (s/keys :req-un {:bar string?}))))}))

;;   (testing "invalid"
;;     (are [form env] (not (c/valid? #'any? (check/type-of form env)))
;;       '(filter even? ["foo" "bar"]) {}
;;       '(filter even? x) {:x (c/parse-spec (s/or :i integer? :s string?))}
;;       '(filter even? x) {:x (c/parse-spec (s/coll-of (s/or :i integer? :s string?)))}
;;       '(filter even? x) {:x (c/parse-spec (s/cat :x integer? :y (s/* string?)))}
;;       '(filter 3 :foo) {})))

;; (deftest filter-return
;;   ;; checks that filter returns correct type for valid calls
;;   (are [expected form env] (c/valid? #'any? (check/type-of form env))
;;     (c/coll-of (c/pred-spec #'integer?)) '(filter identity (range 5)) {}
;;     (c/coll-of (c/pred-spec #'integer?)) '(filter identity coll) {:coll (c/coll-of (c/or- [(c/pred-spec #'integer?) (c/value nil)]))}
;;     (c/value []) '(filter identity nil) {}))
