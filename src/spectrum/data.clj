(ns spectrum.data
  (:require [clojure.core.memoize :as memo]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [clojure.spec.alpha :as s]
            [spectrum.util :refer (print-once protocol? namespace? def-instance-predicate instrument-ns)]))

(defonce var-analysis
  ;; var => ana.jvm/analysis cache
  (atom {}))

(defonce var-specs
  ;; var => spec
  (atom {}))

(defonce var-dependencies
  ;; var => vars
  (atom {}))

(defonce defmethod-analysis
  ;; [var dispatch-value] => analysis cache
  (atom {}))

(defonce java-method-specs
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

(def-instance-predicate reflect-method? clojure.reflect.Method)
(s/fdef add-invoke-transformer :args (s/cat :v (s/alt :v var? :m reflect-method?) :f fn?))
(defn add-invoke-transformer [v f]
  (swap! invoke-transformers assoc v f)
  nil)

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

(s/fdef store-var-dependencies :args (s/cat :v var? :deps (s/coll-of var?)))
(defn store-var-dependencies [v deps]
  (swap! var-dependencies assoc v deps)
  nil)

(defn get-var-dependencies []
  @var-dependencies)

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

(s/fdef get-var-arities :args (s/cat :v var?) :ret (s/nilable ::ana.jvm/analysis))
(defn get-var-arities
  "Return the set of :arglists for this var. Must have been analyzed"
  [v]
  (some->> (get-var-analysis v)
           :init
           :expr))

(defn with-meta? [x]
  (instance? clojure.lang.IObj x))

(s/fdef store-var-spec :args (s/cat :v var? :s :spectrum.conform2/type) :ret nil?)
(defn store-var-spec [v t]
  {:pre [(var? v)]}
  (swap! var-specs assoc v (if (with-meta? t)
                             (with-meta t {:var v})
                             t))
  nil)

(defn get-var-spec [v]
  {:post [(do (when (and % (not (= v (:var %))))
                (println "get-var-spec:" v % (:var %))) true)
          (if %
            (-> % meta :var (= v))
            true)]}
  (get @var-specs v))

(s/def ::reflect-args (s/coll-of class? :kind vector?))
(s/fdef replace-method-spec :args (s/cat :cls class? :name symbol? :args ::reflect-args :spect :spectrum.conform/spect))
(defn replace-method-spec
  "Given a java method replace it
  with the more accurate spec `spec`.

  implicit (c/or nil) will not be added to arguments or return types,
  so if nils are necessary, they must be specified.

  Method args is a vector of classes, same as returned by
  clojure.reflect/reflect :parameter-types. Spec should be an fn-spec

  use this to e.g. indicate a method is always not-nil, regardless of
  args. use `ann` when the return type is dynamic based on the input
  arguments.
"

  [cls method-name method-args spec]
  {:pre [(class? cls)
         (symbol? method-name)
         (vector? method-args)
         (every? class? method-args)]}
  (swap! java-method-specs assoc [cls method-name method-args] spec))

(s/fdef get-updated-method-spec :args (s/cat :cls class? :name symbol? :args ::reflect-args))
(defn get-updated-method-spec [cls method-name method-args]
  (get @java-method-specs [cls method-name method-args]))

(defn reset-cache!
  "Clear cache. Useful for dev"
  []
  (swap! var-analysis (constantly {}))
  (swap! var-specs (constantly {}))
  (swap! analyzed-nses (constantly #{}))
  (memo/memo-clear! (ns-resolve 'spectrum.flow 'flow))
  (memo/memo-clear! (ns-resolve 'spectrum.flow 'cached-infer)))

(instrument-ns)
