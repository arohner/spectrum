(ns spectrum.parse-spec-test
  (:require [clojure.spec.alpha :as s]
            [clojure.test :refer :all]
            [spectrum.parse-spec :as ps]
            [spectrum.types :as t]))

(deftest parse-works
  (are [s ret-pred] (ret-pred (ps/parse-spec (s/form s)))
    (s/spec int?) var?
    (s/* int?) t/seq-t?
    (s/+ int?) t/cat-t?
    (s/cat :i :int?) t/cat-t?
    (s/? string?) t/alt-t?
    ))

(comment
  (deftest parse-everything
    (doseq [[k v] (-> #'s/registry-ref deref deref)]
      (is (ps/parse-spec v) (format "failed to parse %s %s" k (s/form (s/spec k)))))))
