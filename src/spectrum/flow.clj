(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.util :as util]))

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(defn get-fn-spec [v]
  (let [s (s/fn-specs v)]
    (when (not= s empty-fn-spec)
      (c/parse-fn-spec s))))

(defn flow-dispatch [a]
  (:op a))

(s/fdef flow :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)

(defmulti flow
  "Given an analysis, walk and update-in the the analysis attaching ::specs and ::ret to values"
  #'flow-dispatch)

(s/fdef flow-ns :args (s/cat :as ::ana.jvm/analyses) :ret ::ana.jvm/analyses)

(defn flow-ns
  "Given the result of analyze-ns, flow all forms"
  [as]
  (map flow as))

(s/fdef maybe-assoc-var-name :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)
(defn maybe-assoc-var-name
  "Given a def analysis, if the def stores a fn, update the :fn analysis to contain the varname, for future analysis"
  [a]
  (let [path (if (-> a :init :op (= :with-meta))
               [:init :expr]
               [:init])]
    (if (= :fn (:op (get-in a path)))
      (assoc-in a (conj path ::var) (:var a))
      (do
        (println "def not var")
        a))))

(defmethod flow :default [a]
  a)

(defmethod flow :def [a]
  (data/store-var-analysis a)
  (let [a (maybe-assoc-var-name a)]
    (if (-> a :init)
      (assoc a :init (flow (util/zip a :init)))
      a)))

(defmethod flow :with-meta [a]
  (update-in a [:expr] flow))

(s/fdef maybe-assoc-fn-specs :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)

(defmethod flow :fn [a]
  (-> a
      (maybe-assoc-fn-specs)
      (update-in [:methods] (fn [methods]
                              (mapv (fn [m]
                                      (flow (with-meta m {:a a}))) methods)))))

(defmethod flow :do [a]
  (-> a
      (update-in [:statements] (fn [statements] (mapv flow statements)))
      (update-in [:ret] flow)))

(defn destructure-fn-params
  "Given a spect and ana.jvm/fn-method params, update params to include spec"
  [params spec]
  (loop [ret []
         params params
         spec spec]
    (if (seq params)
      (let [param (first params)
            s (c/first* spec)]
        (assert s)
        (if (:variadic? param)
          (conj ret (assoc param ::spec (c/rest* spec)))
          (recur (conj ret (assoc param ::spec s)) (rest params) (c/rest* spec))))
      ret)))

(defmethod flow :fn-method [a]
  (let [v (-> a meta :a ::var)]
    (assert v)
    (if-let [s (get-fn-spec v)]
      (update-in a [:params] destructure-fn-params (:args s))
      (do
        (println "warning: no spec for " v)
        a))))

;; (s/instrument-ns 'spectrum.flow)
