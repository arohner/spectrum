(ns spectrum.util
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]))

(defn literal? [x]
  (let [a (ana.jvm/analyze x)]
    (and (:literal? a) (not= :unknown (:type a)))))

(defn fn-literal? [x]

  (and (seq? x)
       (= 'fn (first x))
       (let [a (ana.jvm/analyze x)]
         (= :fn (:op a)))))

(defn zip
  "Returns (get x key), with x attached as metadata"
  [a key]
  (with-meta (get a key) {:a a}))

(defn with-a [x a]
  (with-meta x {:a a}))

(defn unwrap-a [x]
  (-> x meta :a))

(defn unwrap-while [x f]
  (let [a (unwrap-a)]
    (when a
      (if (f a)
        a
        (recur a f)))))

(defn print-once* [& args]
  (apply println args))

(def print-once (memoize print-once*))
