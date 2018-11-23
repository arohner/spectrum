(ns spectrum.flow2-test
  (:require [clojure.test :refer :all]
            [spectrum.conform :as c]
            [spectrum.flow2 :as f2]))

(def inc-arg (c/or- [(c/class-spec java.lang.Number) (c/class-spec Double/TYPE) (c/class-spec Long/TYPE)]))

(deftest examples
  (are [f ret] (c/valid? ret (f2/infer-form f))
    '(fn [x] 1) (c/fn-spec {:args (c/cat- [(c/pred-spec #'any?)]) :ret (c/value 1)})
    '(fn [x] (inc x)) (c/fn-spec {:args (c/cat- [inc-arg]) :ret inc-arg})
    '(fn [x] (let [y x] (inc y))) (c/fn-spec {:args (c/cat- [inc-arg]) :ret inc-arg})
    '(fn [x] (= x 3)) (c/fn-spec {:args (c/cat- [(c/pred-spec #'any?)]) :ret (c/class-spec Boolean/TYPE)})))
