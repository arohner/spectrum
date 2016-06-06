(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]))

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
  (-> a
      (maybe-assoc-var-name)
      (update-in [:init] flow)))

(defmethod flow :with-meta [a]
  (update-in a [:expr] flow))

(s/fdef maybe-assoc-fn-specs :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)

(defn maybe-assoc-fn-specs
  "Given a :fn analysis that contains ::flow/var, assoc the parsed fn-specs"
  [a]
  (if-let [v (-> a ::var)]
    (if-let [s (get-fn-spec v)]
      (assoc a ::spec s)
      a)
    a))

(defmethod flow :fn [a]
  (-> a
      (maybe-assoc-fn-specs)
      (update-in [:methods] (fn [methods]
                              (mapv flow methods)))))

(defmethod flow :do [a]
  (-> a
      (update-in [:statements] (fn [statements] (mapv flow statements)))
      (update-in [:ret] flow)))

(s/instrument-ns 'spectrum.flow)
