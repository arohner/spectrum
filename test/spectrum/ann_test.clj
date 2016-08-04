(ns spectrum.ann-test
  (:require [clojure.test :refer :all]
            [clojure.spec :as s]
            [spectrum.conform :as c]))

(deftest instance?-transformer
  (is (-> (c/maybe-transform #'instance? (c/parse-spec (s/get-spec #'instance?)) (c/cat- [(c/class-spec String) (c/parse-spec #'string?)])) :ret :v))

  (is (-> (c/maybe-transform #'instance? (c/parse-spec (s/get-spec #'instance?)) (c/cat- [(c/class-spec String) (c/unknown nil)])) :ret (= (c/parse-spec #'boolean?)))))
