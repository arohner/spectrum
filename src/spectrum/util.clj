(ns spectrum.util
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s])
  (:import clojure.lang.Var))

(defn fn-literal? [x]
  (and (seq? x)
       (= 'fn* (first x))))

(s/fdef var-name :args (s/cat :v var?) :ret symbol?)
(defn var-name [^Var v]
  (symbol (str (.ns v)) (str (.sym v))))

(s/fdef strip-namespace :args (s/cat :k keyword?) :ret simple-keyword?)
(defn strip-namespace [k]
  (keyword (name k)))

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
