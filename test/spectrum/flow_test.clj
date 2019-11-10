(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as spec-test]
            [spectrum.conform :as c]
            [spectrum.equations :as eq]
            [spectrum.flow :as f]
            [spectrum.types :as t])
  (:import [clojure.lang IChunk]))

(deftest infer-var
  (are [v] (boolean (do
                      (println "infer-var" v)
                      (f/infer-var v {:dependencies? true})))
    #'apply
    #'clojure.core/reduce1
    #'clojure.core/spread
    #'list*
    #'str
    #'map
    #'true?
    ))

(deftest branch-prediction
  (are [f ret] (c/valid? ret (f/infer-form f))
    '(fn [s] (if (chunked-seq? s) (chunk-first s))) ['fn
                                                     {['cat '?x] ['or [#'nil? ['chunk '?y]]]}]))

(deftest simplify-regex
  (are [e] (s/valid? ::eq/equation (f/simplify-equation e))
    (eq/<= ['cat ['value '?x33] ['not ['value '?x33]]] ['cat '?t2 '?t3])
    (eq/<= ['cat ['value '?x33] ['not ['value '?x33]]] ['cat '?t2 '?t3 '?t4])
    (eq/<= ['cat ['value '?x33]] ['cat '?t2 '?t3 '?t4])))


(defn map-simple
  "Simple implementantion of #'map, for testing "
  [f coll]
  (lazy-seq
   (when-let [s (seq coll)]
     (cons (f (first s)) (map-simple f (rest s))))))

(deftest infer-map
  (f/infer-var #'map-simple))
