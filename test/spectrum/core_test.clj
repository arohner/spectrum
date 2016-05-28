(ns spectrum.core-test
  (:require [clojure.test :refer :all]
            [clojure.spec :as s]
            [spectrum.core :as st]))


(s/def ::even-int (s/and integer? even?))

(deftest parse-spec-works
  (testing "returns Spect"
    (are [spec] (satisfies? st/Spect (st/parse-spec spec))
         'integer?
         (s/spec integer?)
         (s/spec #(< % 10))
         (s/cat :x integer? :y keyword?)
         ::even-int
         (s/spec ::even-int)
         (s/or :int integer? :str string?)
         (s/and #(> % 10))
         (s/and integer? #(> % 10)))))

(defmacro conform-pass [spec args expected]
  `(is (= ~expected (st/conform ~spec ~args))))

(defmacro conform-fail [spec args]
  `(is (nil? (st/conform ~spec ~args))))

(deftest conform-works
  (testing "passing"
    (are [spec val expected] (= expected (st/conform spec val))
         'integer? 3 3
         (s/spec #(< % 10)) 3 3
         'integer? 'integer? (st/parse-spec 'integer?)
         'integer? (s/and integer? even?) (st/parse-spec 'integer?)
         'integer? (s/and integer? even?) (st/parse-spec 'integer?)
         (s/and integer? even?) 10 10
         (s/and integer? even?) (s/and integer? even?) (st/parse-spec (s/and integer? even?))
         (s/and integer? even?) (s/and integer? even? #(> % 10)) (st/parse-spec (s/and integer? even?))
         (s/or :int integer? :str string?) "foo" [:str "foo"]
         (s/or :int integer? :str string?) 'string? [:str (st/parse-spec 'string?)]))

  (testing "should fail"
    (are [spec val] (nil? (st/conform spec val))
         'integer? "foo"
         (s/spec #(< % 10)) 12
         'integer? 'keyword?
         'integer? (s/or :int integer? :str string?)
         (s/and integer? even?) 'integer?
         (s/and integer? even?) 13
         (s/and integer? even? #(> % 10)) (s/and integer? even?))))
