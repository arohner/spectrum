(ns spectrum.data
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.util :refer (print-once protocol?)]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
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
  ^{:doc "Map of vars to transformer functions"}
  type-transformers
  (atom {}))

(defn get-invoke-transformer [v]
  (get @invoke-transformers v))

(defn get-type-transformer [v]
  (get @type-transformers v))

(defonce
  ^{:doc "map of predicates to java classes."}
  pred->class-
  (atom {}))

(defonce
  ^{:doc "map of preds to protocols"}
  pred->protocol-
  (atom {}))

(s/fdef register-pred->class :args (s/cat :p var? :cls class?))
(defn register-pred->class
  "Register pred as checking for instances of class c. Use this for predicaess that are exactly (instance? c x)"
  [pred cls]
  (swap! pred->class- assoc pred cls)
  nil)

(s/fdef register-protocol->pred :args (s/cat :p var? :protocol protocol?))
(defn register-pred->protocol
  "Register pred as checking for protocol p. Use this for predicatess that are exactly equivalent to (satisfies? p x)"
  [pred protocol]
  (swap! pred->protocol- assoc pred protocol)
  nil)

(s/fdef pred->class :args (s/cat :p var?) :ret (s/nilable class?))
(defn pred->class [v]
  (get @pred->class- v))

(s/fdef pred->protocol :args (s/cat :p any?) :ret (s/nilable protocol?))
(defn pred->protocol [v]
  (get @pred->protocol- v))

(s/fdef pred->protocol :args (s/cat :p any?) :ret boolean?)
(defn pred->protocol? [x]
  (boolean (pred->protocol x)))

(defn store-var-analysis
  "Store the ana.jvm/analyze result for a var. Used for future type checking"
  [a]
  (swap! var-analysis assoc (:var a) a))

(defn store-defmethod-analysis
  [a]
  (let [v (-> a :args (get 1) :spectrum.flow/var)
        dispatch-val (-> a :args first :val)]
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
  {:post [(do (when-not %
                (print-once "warning: no var analysis for %s" v)) true)]}
  (get @var-analysis v))

(s/fdef get-var-arities :args (s/cat :v var?) :ret (s/nilable ::ana.jvm/analysis))
(defn get-var-arities
  "Return the set of :arglists for this var. Must have been analyzed"
  [v]
  (some->> (get-var-analysis v)
           :init
           :expr))
