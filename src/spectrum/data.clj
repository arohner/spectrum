(ns spectrum.data)

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
