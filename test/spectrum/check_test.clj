(ns spectrum.check-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer :all]
            [clojure.tools.namespace.find :as find]
            [clojure.spec :as s]
            [clojure.spec.test :as spec-test]
            [spectrum.check :as st]))

(spec-test/instrument)

(defn example-namespaces []
  (find/find-namespaces-in-dir (io/file "test/spectrum/examples")))

;; (deftest clojure-core-no-errors []
;;   (is (= nil (st/check 'clojure.core))))

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
    (testing (str "testing" ns)
      (is (seq (st/check ns))))))
