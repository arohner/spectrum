(ns spectrum.data
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [spectrum.util :refer (print-once protocol?)]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
  (atom {}))

(defonce var-inferred-specs
  ;; var => inferred spec
  (atom {}))

(defonce defmethod-analysis
  ;; [var dispatch-value] => analysis cache
  (atom {}))

(defonce analyzed-nses
  (atom #{}))

(defonce
  ^{:doc "Map of vars to transformer functions"}
  invoke-transformers
  (atom {}))

(defonce
  ^{:doc "Map of specs to extra specs that are true about the spec"}
  extra-dependent-specs (atom {}))

;; current ana.jvm/analysis, if any
(def ^:dynamic *a* nil)

(defn get-invoke-transformer [v]
  (get @invoke-transformers v))

(s/fdef register-dependent-specs :args (s/cat :s :spectrum.conform/spect :dep :spectrum.conform/spect) :ret nil?)
(defn register-dependent-spec
  "Register an extra dependent-spec for spec s.

This is useful for extra properties of the spec e.g. (pred #'string?) -> (class String)
"
  [s dep]
  (swap! extra-dependent-specs update s (fnil conj #{}) dep)
  nil)

(s/fdef get-dependent-specs :args (s/cat :s :spectrum.conform/spect) :ret (s/nilable (s/coll-of :spectrum.conform/spect :kind set?)))
(defn get-dependent-specs [s]
  (get @extra-dependent-specs s))

(defn store-var-analysis
  "Store the ana.jvm/analyze result for a var. Used for future type checking"
  [a]
  (swap! var-analysis assoc (:var a) a))

(defn store-defmethod-analysis
  [a]
  (let [v (-> a :args (get 1) :spectrum.flow/var)
        dispatch-val (or (-> a :args first :val)
                         (-> a :args first :expr :val))]
    (assert v)
    (assert dispatch-val)
    (swap! defmethod-analysis assoc [v dispatch-val] a)))

(defn mark-ns-analyzed! [ns]
  (swap! analyzed-nses conj ns))

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

(defn load-clojure-data
  "fake analysis data for special clojure.core vars that aren't defined in .clj source"
  []
  (swap! var-analysis assoc #'clojure.core/in-ns {:init {:op :fn
                                                         :form '(fake)
                                                         :env {:file "bogus.clj"
                                                               :line 1
                                                               :column 1}
                                                         :methods [{:variadic? false
                                                                    :fixed-arity 1}]}})
  nil)

(defn analyze-cache-ns
  "analyze and store in var cache, but don't flow or check. Useful for clojure.core and other hard to check nses. "
  [ns]
  (let [as (ana.jvm/analyze-ns ns)]
    (doseq [a as]
      (when (= :def (:op a))
        (store-var-analysis a)))
    (mark-ns-analyzed! ns)))

(s/fdef get-var-analysis :args (s/cat :v var?) :ret (s/nilable ::ana.jvm/analysis-def))
(defn get-var-analysis
  [v]
  (get @var-analysis v))

(s/fdef var-analysis? :args (s/cat :v var?) :ret boolean?)
(defn var-analysis?
  "True if we have analysis on v"
  [v]
  (boolean (get @var-analysis v)))

(s/fdef get-var-arities :args (s/cat :v var?) :ret (s/nilable ::ana.jvm/analysis))
(defn get-var-arities
  "Return the set of :arglists for this var. Must have been analyzed"
  [v]
  (some->> (get-var-analysis v)
           :init
           :expr))

(s/fdef store-var-inferred-spec :args (s/cat :v var? :s :spectrum.conform/spect) :ret nil?)
(defn store-var-inferred-spec [v s]
  {:pre [(var? v)
         s]}
  (swap! var-inferred-specs assoc v s)
  nil)

(defn get-var-inferred-spec [v]
  (get @var-inferred-specs v))
