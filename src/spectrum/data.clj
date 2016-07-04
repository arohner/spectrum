(ns spectrum.data
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
  (atom {}))

(defonce checked-nses
  ;; Previously checked namespaces. Will not be rechecked unless checked at the top-level (i.e. not a dep of another ns
  (atom #{}))

(defn store-var-analysis
  "Store the ana.jvm/analyze result for a var. Used for future type checking"
  [a]
  (swap! var-analysis assoc (:var a) a))

(defn load-clojure-data
  "fake analysis data for special clojure.core vars that aren't defined in .clj source"
  []
  (swap! var-analysis assoc #'clojure.core/in-ns {:init {:op :fn
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
