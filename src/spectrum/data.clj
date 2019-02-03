(ns spectrum.data
  (:require [clojure.core.memoize :as memo]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [clojure.spec.alpha :as s]
            [spectrum.types :as t]
            [spectrum.util :refer (print-once protocol? namespace? def-instance-predicate instrument-ns)]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
  (atom {}))

(defonce var-specs
  ;; var => spec
  (atom {}))

(defonce var-annotations
  (atom {}))

(defonce var-dependencies
  ;; var => vars
  (atom {}))

(defonce defmethod-analysis
  ;; [var dispatch-value] => analysis cache
  (atom {}))

(defonce analyzed-nses
  (atom #{}))

;; current ana.jvm/analysis, if any
(def ^:dynamic *a* nil)

(def-instance-predicate reflect-method? clojure.reflect.Method)

(s/def ::a ::ana.jvm/analysis)
(s/def ::path vector?)

(s/fdef get-var-analysis :args (s/cat :v var?) :ret (s/nilable (s/keys :req-un [::a ::path])))
(defn get-var-analysis [v]
  {:pre [(var? v)]}
  (get @var-analysis v))

(s/fdef store-var-analysis :args (s/cat :v var? :a ::ana.jvm/analysis :p vector?))
(defn store-var-analysis
  "Store the ana.jvm/analyze result for a var. Used for future type checking"
  [v a path]
  {:post [(get @var-analysis v)]}
  (assert (var? v))
  (when-not (= :def (get-in a (conj path :op)))
    (println "store-var-analysis:" (get-in a (conj path :op)) (:form a)))
  (assert (= :def (get-in a (conj path :op))))
  (swap! var-analysis assoc v {:a a :path path}))

(defn store-defmethod-analysis
  [a]
  (let [v (-> a :args (get 1) :spectrum.flow/var)
        dispatch-val (or (-> a :args first :val)
                         (-> a :args first :expr :val))]
    (assert v)
    (assert dispatch-val)
    (swap! defmethod-analysis assoc [v dispatch-val] a)))

(s/fdef mark-ns-analyzed! :args (s/cat :ns namespace?))
(defn mark-ns-analyzed! [ns]
  (swap! analyzed-nses conj ns))

(s/fdef mark-ns-analyzed! :args (s/cat :ns namespace?))
(defn mark-ns-unanalyzed! [ns]
  (swap! analyzed-nses disj ns))

(s/fdef analyzed-ns? :args (s/cat :ns namespace?) :ret boolean?)
(defn analyzed-ns? [ns]
  (contains? @analyzed-nses ns))

(defn get-defmethod-analysis [v dispatch]
  (get @defmethod-analysis [v dispatch]))

(defn get-defmethod-fn-analysis
  "Returns the flow for only the fn, not the whole (. var addMethod f)"
  [v dispatch]
  (get-in (get-defmethod-analysis v dispatch) [:args 1]))

(defn get-defmethod-fn-method-analysis
  "Returns the flow for only the fn, not the whole (. var addMethod f)"
  [v dispatch]
  (get-in (get-defmethod-analysis v dispatch) [:args 1]))

(s/fdef var-analysis? :args (s/cat :v var?) :ret boolean?)
(defn var-analysis?
  "True if we have analysis on v"
  [v]
  (boolean (get @var-analysis v)))

(defn with-meta? [x]
  (instance? clojure.lang.IObj x))

(s/fdef store-var-spec :args (s/cat :v var? :s ::t/type) :ret nil?)
(defn store-var-spec [v t]
  {:pre [(var? v)]}
  (swap! var-specs assoc v (if (with-meta? t)
                             (with-meta t {:var v})
                             t))
  nil)

(defn get-var-spec [v]
  {:post [(if %
            (-> % meta :var (= v))
            true)]}
  (get @var-specs v))

(s/fdef ann :args (s/cat :m (s/or :v var? :m (s/tuple class? symbol?)) :t ::t/type))
(defn ann
  "Define a more specific type for the var. `ann` types are preferred
  over explicit specs or inferred types, and if an `ann` exists for a
  var, only it will be consulted"
  [v t]
  (swap! var-annotations assoc v t)
  nil)

(s/fdef get-ann :args (s/cat :x (s/or :v var? :m (s/tuple class? symbol?))) :ret (s/nilable ::t/type))
(defn get-ann [x]
  (get @var-annotations x))

(defn reset-cache!
  "Clear cache. Useful for dev"
  []
  (swap! var-analysis (constantly {}))
  (swap! var-specs (constantly {}))
  (swap! analyzed-nses (constantly #{}))
  (memo/memo-clear! (ns-resolve 'spectrum.flow 'flow))
  (memo/memo-clear! (ns-resolve 'spectrum.flow 'cached-infer)))

(instrument-ns)
