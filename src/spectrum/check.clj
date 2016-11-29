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

(declare check)

;; clojure.spec isn't in the check list atm, because analyzer re-evals the protocols, which breaks e.g. (satsifies? s/Spec) checking

(def builtin-nses '[clojure.core clojure.set clojure.string])

(defn maybe-load-clojure-builtins []
  (when-not (data/analyzed-ns? 'clojure.core)
    (println "loading clojure")
    (data/load-clojure-data)
    (doseq [n builtin-nses]
      (data/analyze-cache-ns n))))

(s/fdef check :args (s/cat :ns symbol?) :ret ::check-errors)

(defn check [ns]
  (maybe-load-clojure-builtins)
  (println "checking " ns)
  (some->>
   (ana.jvm/analyze-ns ns)
   (map flow/flow)
   (mapcat check*)
   (filter identity)))

(s/fdef get-var-analysis :args (s/cat :v var?) :ret (s/nilable ::flow/analysis?))
(defn get-var-analysis
  "Return the fn analysis for a var"
  [v]
  (some-> (data/get-var-analysis v)
          :init
          flow/maybe-strip-meta))

(s/fdef var-analysis? :args (s/cat :v var?) :ret boolean?)
(defn var-analysis?
  "True if we have analysis on v"
  [v]
  (boolean (get @data/var-analysis v)))

(s/fdef a-multimethod? :args (s/cat :a ::ana.jvm/analysis) :ret boolean?)
(defn a-multimethod? [a]
  (and (-> a :init :op (= :new))
       (-> a :init :class :val (= clojure.lang.MultiFn))))

(s/fdef var-fn? :args (s/cat :v var?) :ret boolean?)
(defn var-fn?
  "True if this var holds a fn"
  [v]
  (let [a (get @data/var-analysis v)]
    (when-not a
      (println (format "Couldn't find var %s in analysis cache:" v)))
    (or (-> a :init flow/maybe-strip-meta :op (= :fn))
        (a-multimethod? a))))

(s/fdef wrong-number-args-error :args (s/cat :f ::flow/analysis :a ::flow/analysis) :ret check-error?)
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

(s/fdef check-invoke-fn-spec :args (s/cat :v var? :s c/fn-spec? :a ::flow/analysis))
(defn check-invoke-fn-spec
  [v s a]
  (let [a-args (zip a :args)
        args-spec (flow/analysis-args->spec a-args)
        valid? (c/valid-invoke? s args-spec)]
    (when-not valid?
      (new-error {:message (format "invoke of %s does not conform. expected %s, got %s. " v (print-str (-> s :args)) (print-str args-spec))} a))))

(s/fdef check-invoke-var :args (s/cat :a ::flow/analysis) :ret ::check-errors)
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
      (if-let [s (c/get-var-fn-spec v)]
        (check-invoke-fn-spec v s a)
        (print-once "check-invoke-var: no spec for" v))]
     (filter identity))))

(defn check-invoke-invoke [a]
  (println "check-invoke-invoke:" (:form a) (:op a)))

(defn check-invoke-local [a]
  (print-once "check-invoke-local todo"))

(defn check-invoke-fn-literal [a]
  (print-once "check-invoke-fn-literal todo"))

(defn check-invoke-map [a]
  (print-once "check-invoke-map todo"))

(s/fdef check-walk :args (s/cat :a ::flow/analysis) :ret ::check-errors)
(defn check-walk [a]
  (try
    (mapcat (fn [c-name]
              (let [c (get a c-name)]
                (if (sequential? c)
                  (mapcat (fn [x]
                            (check* (with-a x a))) c)
                  (check* (with-a c a))))) (:children a))
    (catch Exception e
      (println "Exception at" (flow/a-loc-str a) (:form a) (.getMessage e))
      (throw e))))

(defmethod check* :default [a]
  (check-walk a))

(defmethod check* :invoke [a]
  (let [f (-> a :fn flow/maybe-strip-meta)]
    (concat (check-walk a)
            (condp = (:op f)
              :var (check-invoke-var a)
              :fn (check-invoke-fn-literal a)
              :map (check-invoke-map a)
              :local (check-invoke-local a)
              :invoke (check-invoke-invoke a)
              (println "unknown invoke expr" (:form a) (:op a))))))



(defn check-fn-method-return [method-a]
  (let [f (unwrap-a method-a)
        v (::flow/var f)]
    (when v
      (let [ret-spec (:ret (c/get-var-fn-spec v))
            body (-> method-a :body)
            last-expr (if (map? body)
                        body
                        (do
                          (assert (sequential? body))
                          (last body)))
            expr-spec (::flow/ret-spec method-a)]
        (when (and ret-spec (c/known? ret-spec))
          (if expr-spec
            (when-not (c/valid-return? ret-spec expr-spec)
              [(new-error {:message (format "%s return value does not conform. Expected %s, Got %s" (or v "fn") (print-str ret-spec) (print-str expr-spec))} method-a)])
            [(new-error {:message (format "check-fn-method-return no ret-spec for expression:" (:form last-expr))} last-expr)]))))))

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
        [(new-error {:message (format "fn spec doesn't match arity: %s, %s vs. %s" f-var (params-str a) (print-str args-spec))} a)]))))

(defmethod check* :fn-method [a]
  (concat
   (check-walk a)
   (check-fn-method-return a)
   (check-spec-arity a)))

(defn a->java-static-method-name [a]
  (str (:class a) "/" (:method a)))

(defn java-methods-str [cls method]
  (->> (flow/get-java-method cls method)
       (mapv :parameter-types)
       (str/join ", ")))

(s/fdef java-call :args (s/cat :a ::flow/analysis) :ret ::check-errors)
(defn maybe-check-defmethod [a]
  (if (flow/defmethod? a)
    (let [[dispatch-val f] (:args a)]
      ;; TODO flow-default, check-default, :children. defmethod checking is broken because we don't recurse automatically.
      ;;
      )
    nil))

(s/fdef java-call :args (s/cat :a ::flow/analysis) :ret ::check-errors)
(defn java-call [a]
  (let [a-args (zip a :args)
        args-spec (flow/analysis-args->spec a-args)
        call-spec (::flow/args-spec a)]
    (concat
     (if call-spec
       (if (c/known? call-spec)
         (if args-spec
           (let [valid? (c/valid? call-spec args-spec)]
             (when-not valid?
               [(new-error {:message (format "Java Method %s cannot be called with args %s. Expected %s" (a->java-static-method-name a) (print-str args-spec) (print-str call-spec))} a)]))
           (println "static-call no arg-spec:" (flow/a-loc-str a)))
         [(new-error {:message (format "Calling Java method %s unknown spec, given %s, possible: %s" (a->java-static-method-name a) (print-str args-spec) (java-methods-str (:class a) (:method a)))} a)])
       [(new-error {:message (format "Calling Java method: no compatible args for %s. Given %s Possible: %s" (a->java-static-method-name a) (print-str args-spec) (java-methods-str (:class a) (:method a)))} a)])
     (maybe-check-defmethod a))))

(defmethod check* :instance-call [a]
  (concat
   (check-walk a)
   (java-call a)))

(defmethod check* :static-call [a]
  (concat
   (check-walk a)
   (java-call a)))

;; check recur values conform to bindings

(defn analyze-form [form]
  (flow/flow (ana.jvm/analyze form)))

(defn analyze-ns [ns]
  (mapv flow/flow (ana.jvm/analyze-ns ns)))

(defn ensure-analysis [ns]
  (when-not (data/analyzed-ns? ns)
    (println "analyzing" ns)
    (analyze-ns ns)
    (data/mark-ns-analyzed! ns)))

(defn type-of
  "Given a quoted form, returns spectrum's expected type for evaluating the form"
  [f]
  (->> f
       (analyze-form)
       ::flow/ret-spec))

(defn check-form
  "Given a quoted form, returns any typechecking errors, or nil"
  [f]
  (->> f
       (analyze-form)
       (check*)))
