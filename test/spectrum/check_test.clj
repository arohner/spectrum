(ns spectrum.check-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer :all]
            [clojure.tools.namespace.find :as find]
            [clojure.spec :as s]
            [spectrum.core :as st]))

(defn example-namespaces []
  (find/find-namespaces-in-dir (io/file "test/examples")))

;; (deftest clojure-core-no-errors []
;;   (is (= nil (st/check 'clojure.core))))

(deftest in-ns-works
  (st/load-clojure-data)
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
    (is (seq (st/check ns)))))
