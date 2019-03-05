(ns spectrum.check
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pprint :refer (pprint)]
            [clojure.reflect :as reflect]
            [clojure.string :as str]
            [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.analyzer :as analyzer]
            [spectrum.classpath :as classpath]
            [spectrum.types :as t]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.flow :as flow]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)]))

(defrecord CheckError [message file line column end-column])

(s/def ::message string?)

(s/fdef check-error? :args (s/cat :x any?) :ret boolean?)
(defn check-error? [x]
  (instance? CheckError x))

(s/fdef map->CheckError :args (s/cat :m (s/keys :req-un [::message])) :ret check-error?)

(s/fdef new-error :args (s/cat :data (s/keys :req-un [::message]) :a ::flow/analysis) :ret check-error?)
(defn new-error [{:keys [message form data] :as args} a]
  (map->CheckError (merge args (select-keys (:env a) [:file :line :column]))))

(s/def ::maybe-check-error (s/nilable check-error?))

(s/def ::check-errors (s/* check-error?))

(def builtin-nses '[clojure.core clojure.set clojure.string clojure.spec.alpha clojure.spec.gen.alpha])

(defn maybe-load-clojure-builtins []
  (when-not (data/analyzed-ns? (find-ns 'clojure.core))
    (println "loading clojure")
    (doseq [n builtin-nses]
      (flow/analyze-cache-ns n))
    (flow/analyze-cache-resource (io/resource "clojure/core_deftype.clj"))))

(s/fdef check :args (s/cat :ns symbol?) :ret ::check-errors)

(defn check-var [v]
  (maybe-load-clojure-builtins)
  (let [t (flow/infer-var v)]
    ;; (if-let [s ()])
    ))

;; (defn check-ns [ns]
;;   (maybe-load-clojure-builtins)
;;   (println "checking " ns)
;;   (some->>
;;    (analyzer/analyze-ns-1 ns (ana.jvm/empty-env))
;;    (map flow/infer)
;;    (mapcat check*)
;;    (filter identity)))
