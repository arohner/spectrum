(ns spectrum.data
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.util :refer (print-once)]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
  (atom {}))

(defonce checked-nses
  ;; Previously checked namespaces. Will not be rechecked unless checked at the top-level (i.e. not a dep of another ns
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
  ^{:doc "map of preds to java classes."}
  pred->class-
  (atom {}))

(s/fdef register-class-pred :args (s/cat :p var? :cls class?))
(defn register-pred->class
  "Register pred as checking for instances of class c. Use this for preds that correspond *directlly* to classes. "
  [pred cls]
  (swap! pred->class- assoc pred cls)
  nil)

(s/fdef pred->class :args (s/cat :p var?) :ret (s/nilable class?))
(defn pred->class [v]
  (get @pred->class- v))

(defn store-var-analysis
  "Store the ana.jvm/analyze result for a var. Used for future type checking"
  [a]
  (swap! var-analysis assoc (:var a) a))

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
        (store-var-analysis a)))))

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
