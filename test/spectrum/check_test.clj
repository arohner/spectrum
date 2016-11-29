(ns spectrum.check-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer :all]
            [clojure.tools.namespace.find :as find]
            [clojure.spec :as s]
            [clojure.spec.test :as spec-test]
            [spectrum.conform :as c]
            [spectrum.check :as st]))

(spec-test/instrument)

(defn example-namespaces []
  (find/find-namespaces-in-dir (io/file "test/spectrum/examples")))

(deftest in-ns-works
  (st/maybe-load-clojure-builtins)
  (is (st/var-fn? #'clojure.core/in-ns)))

(deftest test-examples-good
  (doseq [ns (->> (example-namespaces)
                  (filter (fn [sym]
                            (re-find #"^spectrum\.examples\.good." (name sym)))))]
    (testing (name ns)
      (is (= nil (seq (st/check ns)))))))

(deftest test-examples-bad
  (doseq [ns (->> (example-namespaces)
                  (filter (fn [sym]
                            (re-find #"^spectrum\.examples\.bad." (name sym)))))]
    (testing (str "testing: " ns)
      (is (seq (st/check ns))))))

;; can't check anything with defprotocol/defrecord yet, requires pods.
(def self-checking-nses [;; 'spectrum.conform
                         ;;'spectrum.flow
                         ;; 'spectrum.check
                         ])
(deftest test-self
  (st/ensure-analysis 'spectrum.analyzer-spec)
  (doseq [ns self-checking-nses]
    (testing (str "testing: " ns)
      ;; currently only testing for non-explosion. Testing for no errors is on the roadmap!
      (st/check ns))))

(deftest type-of-works
  (are [form expected] (= (st/type-of form) expected)
    '3 (c/value 3)))

(deftest check-form-works
  (testing "good"
    (are [form] (nil? (seq (st/check-form form)))
      '(+ 1 3)))
  (testing "bad"
    (are [form] (seq (st/check-form form))
      '(first 1))))
