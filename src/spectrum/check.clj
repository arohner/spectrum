(ns spectrum.check
  (:require [clojure.pprint :as pprint :refer (pprint)]
            [clojure.reflect :as reflect]
            [clojure.string :as str]
            [clojure.spec :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.ann :as ann]
            [spectrum.data :as data]
            [spectrum.flow :as flow]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)]))

(defrecord CheckError [message file line column end-column])

(s/def ::message string?)

(s/fdef check-error? :args (s/cat :x any?) :ret boolean?)
(defn check-error? [x]
  (instance? CheckError x))

(ann/ann #'check-error? (ann/instance-transformer CheckError))

(s/fdef map->CheckError :args (s/cat :m (s/keys :req-un [::message])) :ret check-error?)

(s/fdef new-error :args (s/cat :data (s/keys :req-un [::message]) :a ::flow/analysis) :ret check-error?)
(defn new-error [{:keys [message form data] :as args} a]
  (map->CheckError (merge args (select-keys (:env a) [:file :line :column]))))

(s/def ::maybe-check-error (s/nilable check-error?))

(s/def ::check-errors (s/* check-error?))

(s/fdef check* :args (s/cat :a ::flow/analysis) :ret ::check-errors)

(defmulti check* "Entrypoint into low level checking. Takes a tools.analyzer expression. Returns nil or an error" :op)

(defmethod check* :default [a]
  (print-once (str "TODO check " (:op a)))
  nil)

(declare check)

;; clojure.spec isn't in the check list atm, because analyzer re-evals the protocols, which breaks e.g. (satsifies? s/Spec) checking

(def builtin-nses '[clojure.core clojure.set clojure.string])

(defn maybe-load-clojure-builtins []
  (when-not (contains? @data/checked-nses 'clojure.core)
    (println "loading clojure")
    (data/load-clojure-data)
    (doseq [n builtin-nses]
      (data/analyze-cache-ns n)
      (swap! data/checked-nses conj n))))

(s/fdef check :args (s/cat :ns symbol?) :ret ::check-errors)

(defn check [ns]
  (swap! data/checked-nses conj ns)
  (maybe-load-clojure-builtins)
  (println "checking " ns)
  (some->>
   (ana.jvm/analyze-ns ns)
   (map flow/flow)
   (mapcat check*)
   (doall)
   (filter identity)
   (doall)))

(s/fdef get-var-analysis :args (s/cat :v var?) :ret ::flow/analysis?)
(defn get-var-analysis
  "Return the fn analysis for a var"
  [v]
  (-> @data/var-analysis
      (get v)
      :init
      flow/maybe-strip-meta))

(s/fdef var-fn? :args (s/cat :v var?) :ret boolean?)
(defn var-analysis?
  "True if we have analysis on v"
  [v]
  (boolean (get @data/var-analysis v)))

(s/fdef var-fn? :args (s/cat :v var?) :ret boolean?)
(defn var-fn?
  "True if this var holds a fn"
  [v]
  (let [a (get @data/var-analysis v)]
    (when-not a
      (println (format "Couldn't find var %s in analysis cache:" v)))
    (-> a :init flow/maybe-strip-meta :op (= :fn))))

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
  (let [a-args (zip a :args)
        args-spec (flow/analysis-args->spec a-args)
        valid? (c/valid-invoke? s args-spec)]
    (when-not valid?
      (new-error {:message (format "Function %s cannot be called with args %s. Expected %s" name (c/pretty-str args-spec) (c/pretty-str (-> s :args)))} a))))

(defn check-invoke-var [a]
  (let [v (-> a :fn :var)
        va (get-var-analysis v)]
    (->>
     [(when-not va
        (print-once "warning: no analysis for" v))
      (when (and va (not (var-fn? v)))
        (new-error {:message (format "attempt to call non-fn var: %s" (:form a))} a))
      (when va
        (check-invoke-fn-arity (get-var-analysis v) a))
      (if-let [s (flow/get-var-fn-spec v)]
        (check-invoke-fn-spec (str v) s a)
        (print-once "check-invoke-var: no spec for" v))]
     (filter identity))))

(defn check-invoke-local [a]
  (print-once "check-invoke-local todo"))

(defn check-invoke-fn-literal [a]
  (print-once "check-invoke-fn-literal todo"))

(defn check-invoke-map [a]
  (print-once "check-invoke-map todo"))

(defmethod check* :invoke [a]
  (let [f (-> a :fn flow/maybe-strip-meta)]
    (condp = (:op f)
      :var (check-invoke-var a)
      :fn (check-invoke-fn-literal a)
      :map (check-invoke-map a)
      :local (check-invoke-local a)
      (println "unknown invoke expr" a))))

(defmethod check* :do [a]
  (some->>
   (concat
    (mapcat (fn [s]
              (check* (with-a s a))) (:statements a))
    [(check* (zip a :ret))])
   (doall)
   (filter identity)))

(defmethod check* :let [a]
  (concat
   (mapcat (fn [b]
             (check* (with-a b a))) (:bindings a))
   (check* (zip a :body))))

(defmethod check* :with-meta [a]
  (check* (zip a :expr)))

(defmethod check* :def [a]
  (when (:init a)
    (check* (with-a (:init a) a))))

(defn check-fn-method-return [method-a]
  (let [f (unwrap-a method-a)
        f-var (::flow/var f)
        ret-spec (:ret (flow/get-var-fn-spec f-var))
        body (-> method-a :body)
        last-expr (if (map? body)
                    body
                    (do
                      (assert (sequential? body))
                      (last body)))
        expr-spec (::flow/ret-spec last-expr)]
    (if (and ret-spec (not (c/unknown? ret-spec)))
      (if expr-spec
        (when-not (c/valid-return? ret-spec expr-spec)
          [(new-error {:message (format "%s return value does not conform. Expected %s, Got %s" (or f-var "fn") (c/pretty-str ret-spec) (c/pretty-str expr-spec))} method-a)])
        (println "check-fn-method-return no ret-spec for expression:" (:form last-expr) "@" (flow/a-loc-str last-expr)))
      (println "check-fn-method-return no ret-spec for fn" f-var))))

(defmethod check* :fn [a]
  (concat
   (some->>
    (mapcat (fn [m]
              (check* (with-a m a))) (:methods a))
    (doall)
    (filter identity))))

(defn params-str [a]
  (->> a :params (mapv :form)))

(defn check-spec-arity [a]
  (let [f (unwrap-a a)
        f-var (::flow/var f)
        args-spec (:args (c/parse-spec (s/get-spec f-var)))
        params (:params a)]
    (assert params)
    (when args-spec
      (when-not (flow/arity-conform? args-spec params)
        [(new-error {:message (format "fn spec doesn't match arity: %s, %s vs. %s" f-var (params-str a) (c/pretty-str args-spec))} a)]))))

(defmethod check* :fn-method [a]
  (let [body (zip a :body)]
    (concat
     (check* body)
     (check-fn-method-return a)
     (check-spec-arity a))))

(defmethod check* :quote [a])

(defn a->java-static-method-name [a]
  (str (:class a) "/" (:method a)))

(defn java-methods-str [cls method]
  (->> (flow/get-java-method cls method)
       (mapv :parameter-types)
       (str/join ", ")))

(defmethod check* :static-call [a]
  (let [a-args (zip a :args)
        args-spec (flow/analysis-args->spec a-args)
        call-spec (::flow/args-spec a)]
    (if call-spec
      (if (c/known? call-spec)
        (if args-spec
          (let [valid? (c/valid? call-spec args-spec)]
            (when-not valid?
              [(new-error {:message (format "Java Method %s cannot be called with args %s. Expected %s" (a->java-static-method-name a) (c/pretty-str args-spec) (c/pretty-str call-spec))} a)]))
          (println "static-call no arg-spec:" (flow/a-loc-str a)))
        [(new-error {:message (format "Calling Java method %s unknown spec, given %s, possible: %s" (a->java-static-method-name a) (c/pretty-str args-spec) (java-methods-str (:class a) (:method a)))} a)])
      [(new-error {:message (format "Calling Java method: no compatible args for %s. Given %s Possible: %s" (a->java-static-method-name a) (c/pretty-str args-spec) (java-methods-str (:class a) (:method a)))} a)])))

;; check recur values conform to bindings
