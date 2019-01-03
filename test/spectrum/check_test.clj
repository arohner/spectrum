(ns spectrum.check-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer :all]
            [clojure.tools.namespace.find :as find]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as spec-test]
            [spectrum.conform :as c]
            [spectrum.check :as st]
            [spectrum.flow :as flow]
            [spectrum.util :as util]))

(util/instrument-in-CI)

;; (defn example-namespaces []
;;   (find/find-namespaces-in-dir (io/file "test/spectrum/examples")))

;; (deftest in-ns-works
;;   (st/maybe-load-clojure-builtins)
;;   (is (flow/var-fn? #'clojure.core/in-ns)))

;; (deftest test-examples-good
;;   (doseq [ns (->> (example-namespaces)
;;                   (filter (fn [sym]
;;                             (re-find #"^spectrum\.examples\.good." (name sym)))))]
;;     (testing (name ns)
;;       (is (= nil (seq (st/check ns)))))))

;; (deftest test-examples-bad
;;   (doseq [ns (->> (example-namespaces)
;;                   (filter (fn [sym]
;;                             (re-find #"^spectrum\.examples\.bad." (name sym)))))]
;;     (testing (str "testing: " ns)
;;       (is (seq (st/check ns))))))

;; ;; can't check spectrum.conform until we figure out a way to handle the reify issue
;; (def self-checking-nses ['spectrum.java
;;                          ;; 'spectrum.conform
;;                          'spectrum.flow
;;                          'spectrum.ann
;;                          'spectrum.check])

;; (deftest test-self
;;   (flow/ensure-analysis 'spectrum.analyzer-spec)
;;   (doseq [ns self-checking-nses]
;;     (testing (str "testing: " ns)
;;       ;; currently only testing for non-explosion. Testing for no errors is on the roadmap!
;;       (st/check ns))))

;; ;; (deftest test-clojure
;; ;;   (st/check 'clojure.core))

;; (deftest type-of-works
;;   (testing "truthy"
;;     (are [form expected] (= (st/type-of form) expected)
;;       '3 (c/value 3)))
;;   (testing "falsey"
;;     ;; (are [form args] (c/invalid? (st/type-of form args))
;;     ;;   ;; FIXME. Technically correct according to java specs. Need a way to override java type signature w/ more specific spec.
;;     ;;   ;; '(inc x) {:x (c/pred-spec #'string?)}
;;     ;;   )
;;     ))

;; (deftest check-form-works
;;   (testing "good"
;;     (are [form] (nil? (seq (st/check-form form)))
;;       '(+ 1 3)))
;;   (testing "bad"
;;     (are [form] (seq (st/check-form form))
;;       '(first 1))))
