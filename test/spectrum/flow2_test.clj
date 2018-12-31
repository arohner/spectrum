(ns spectrum.flow2-test
  (:require [clojure.test :refer :all]
            [spectrum.conform :as c]
            [spectrum.flow2 :as f2]))

(def inc-arg (c/or- [(c/class-spec java.lang.Number) (c/class-spec Double/TYPE) (c/class-spec Long/TYPE)]))

(deftest examples
  (testing "truthy"
    (are [f ret] (c/valid? ret (f2/infer-form f))
;;; basic inference
      '(fn [x] 1) (c/fn-spec {:args (c/cat- [(c/pred-spec #'any?)]) :ret (c/value 1)})
      '(fn [x] (inc x)) (c/fn-spec {:args (c/cat- [inc-arg]) :ret inc-arg})
      '(fn [x] (let [y x] (inc y))) (c/fn-spec {:args (c/cat- [inc-arg]) :ret inc-arg})
      '(fn [x] (= x 3)) (c/fn-spec {:args (c/cat- [(c/pred-spec #'any?)]) :ret (c/class-spec Boolean/TYPE)})))
  (testing "falsey"
    (are [f] (= nil (f2/infer-form f))
;;; basic inference
      '(fn [x] (inc "foo")))))

(deftest seq
  (testing "truthy"
    (are [x ret] (c/valid? ret (f2/infer-form '(seq x) {:x x}))
      (c/coll-of (c/pred-spec #'int?)) (c/seq-of (c/pred-spec #'int?))
      (c/map-of (c/pred-spec #'keyword?) (c/pred-spec #'string?)) (c/seq-of (c/tuple #'int?))
  (testing "falsey"
    (are [x] (= nil (f2/infer-form '(seq x) {:x x}))
      (c/pred-spec #'int?))))

;; seq

;; first

;; rest

;; get

;; assoc

;; get-in

;; assoc-in

;; update-in
