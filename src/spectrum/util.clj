(ns spectrum.util
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]))

(defn literal? [x]
  (let [a (ana.jvm/analyze x)]
    (and (:literal? a) (not= :unknown (:type a)))))

(defn fn-literal? [x]
  (let [a (ana.jvm/analyze x)]
    (= :fn (:op a))))
