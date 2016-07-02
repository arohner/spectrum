(ns spectrum.check
  (:require [clojure.reflect :as reflect]
            [clojure.string :as str]
            [clojure.spec :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.flow :as flow]
            [spectrum.util :as util :refer (zip with-a unwrap-a)]))

(defrecord CheckError [message file line column end-column])

(defn new-error [{:keys [message form data] :as args} a]
  (map->CheckError (merge args (select-keys (:env a) [:file :line :column]))))

(defn check-error? [x]
  (instance? CheckError x))

(s/def ::maybe-check-error (s/nilable check-error?))

(s/def ::check-errors (s/* check-error?))

(s/fdef check* :args (s/cat :a ::ana.jvm/analysis) :ret ::check-errors)

(defmulti check* "Entrypoint into low level checking. Takes a tools.analyzer expression. Returns nil or an error" :op)

(defmethod check* :default [a]
  nil)

(declare check)

(def builtin-nses '[clojure.core clojure.set clojure.string clojure.spec])

(defn maybe-load-clojure-builtins []
  (when-not (contains? @data/checked-nses 'clojure.core)
    (println "loading clojure")
    (data/load-clojure-data)
    (doseq [n builtin-nses]
      (println "flow:" n)
      (doall (flow/flow-ns (ana.jvm/analyze-ns n)))
      (println "flow:" n "done")
      (swap! data/checked-nses conj n))))

(s/fdef check :args (s/cat :ns symbol?) :ret ::check-errors)

(defn check [ns]
  (swap! data/checked-nses conj ns)
  (maybe-load-clojure-builtins)
  (println "checking " ns)
  (->>
   (ana.jvm/analyze-ns ns)
   (map flow/flow)
   (mapcat check*)
   (filter identity)
   (doall)))

(s/fdef get-var-arities :args (s/cat :v var?) :ret (s/nilable ::flow/analysis))
(defn get-var-arities
  "Return the set of :arglists for this var. Must have been analyzed"
  [v]
  (some->> (get-in data/var-analysis v)
           :init
           :expr))

(s/fdef maybe-strip-meta :args ::flow/analysis :ret ::flow/analysis)
(defn maybe-strip-meta
  "If a is a :op :with-meta, strip it and return the :expr, or a"
  [a]
  (if (-> a :op (= :with-meta))
    (-> a :expr)
    a))

(s/fdef var-fn? :args (s/cat :v var?) :ret boolean?)
(defn var-fn?
  "True if this var holds a fn"
  [v]
  (let [a (get @data/var-analysis v)]
    (when-not a
      (println (format "Couldn't find var %s in analysis cache:" v)))
    (-> a :init maybe-strip-meta :op (= :fn))))

(s/fdef get-var-analysis :args (s/cat :v var?) :ret ::flow/analysis?)
(defn get-var-analysis
  "Return the fn analysis for a var"
  [v]
  (-> @data/var-analysis
      (get v)
      :init
      maybe-strip-meta))

(defn wrong-number-args-error [f a]
  (let [arities (-> f :methods (->> (map :arglist) (str/join " or ")))]
    (new-error {:message (format "Function %s called with incorrect number of args. Expected %s, got %s" (-> a :form first) arities (->> a :form rest vec))} a)))

(defn check-invoke-fn-arity
  "check the fn invoke for correct arity. Takes the :fn analysis, and the caller args"
  [f a]
  (let [args (:args a)
        valid? (some (fn [m]
                       (or (and (not (:variadic? m))
                                (= (count args) (:fixed-arity m)))
                           (and (:variadic? m)
                                (>= (count args) (:fixed-arity m))))) (-> f :methods))]
    (when-not valid?
      (wrong-number-args-error f a))))

(defn check-invoke-fn-spec
  [name s a]
  (println "check invoke-fn-spec")
  (let [a-args (zip a :args)
        args (analysis->args a-args)
        valid? (c/valid? (:args s) args)]
    (when-not valid?
      (new-error {:message (format "Function %s cannot be called with args %s. Expected %s" name (vec args) (-> s :args :forms))} a))))

(defn check-invoke-var [a]
  (let [v (-> a :fn :var)]
    (->>
     [(when-not (var-fn? v)
        (new-error {:message (format "attempt to call non-fn var: %s" (:form a))} a))
      (check-invoke-fn-arity (get-var-analysis v) a)
      (if-let [s (flow/get-var-fn-spec v)]
        (check-invoke-fn-spec (str v) s a)
        (println "no spec for" v))]
     (filter identity))))

(defn check-invoke-local [a]
  (println "check-invoke-local todo"))

(defn check-invoke-fn-literal [a]
  (println "check-invoke-fn-literal todo"))

(defn check-invoke-map [a]
  (println "check-invoke-map todo"))

(defmethod check* :invoke [a]
  (let [f (-> a :fn maybe-strip-meta)]
    (condp = (:op f)
      :var (check-invoke-var a)
      :fn (check-invoke-fn-literal a)
      :map (check-invoke-map a)
      :local (check-invoke-local a)
      (println "unknown invoke expr" a))))



(defmethod check* :do [a]
  (->>
   (concat
    (mapcat (fn [s]
              (check* (with-a s a))) (:statements a))
    [(check* (zip a :ret))])
   (filter identity)))

(defmethod check* :with-meta [a]
  (check* (zip a :expr)))

(defmethod check* :def [a]
  (check* (zip a :init)))

(defmethod check* :fn [a]
  (->>
   (mapcat (fn [m]
             (check* (with-a m a))) (:methods a))
   (filter identity)))

(defmethod check* :fn-method [a]
  ;; (println "check fn method:" a)
  (check* (zip a :body)))

(defmethod check* :quote [a])
