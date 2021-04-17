(ns spectrum.compiler
  (:refer-clojure :exclude [ancestors compile descendants type cast])
  (:require [clojure.core :as core]
            [clojure.math.combinatorics :as combo]
            [clojure.test.check.generators :as gen]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as sgen]
            [clojure.set :as set]
            [hashp.core]
            [spectrum.analyzer :as analyzer]
            [spectrum.data :as data]
            [spectrum.java :as java]
            [spectrum.util :refer [instrument-ns validate! namespace? atom?]])
  (:import [clojure.lang Symbol Keyword Var IPersistentMap]))

(def types-hierarchy (atom (make-hierarchy)))

(def type-counter (atom 0))

(defprotocol Type
  (type [this]
    "Returns")
  (cast* [this type]
    "Cast this type to `:type, one of #{:java :spec :regex :value}`")
  (truthy* [this]
    "Return :true :false or :undecided if this type appears in the
    test of an `if`")
  (invokeable* [this]
    "true if this can be invoked")
  (valid* [this right]))

(defn type? [x]
  (satisfies? Type x))

(s/def ::type type?)

(defn ! [x]
  (assert (identity x))
  x)

(defn first! [x]
  (assert (seq x) (print-str "expected seq, got" (class x)))
  (assert (= 1 (count x)))
  (first x))

(s/fdef cast :args (s/cat :t type? :k keyword?) :ret type?)
(defn cast [t tag]
  (cast* t tag))

(s/fdef truthy args (s/cat :t type?) :ret #{:true :false :undecided})
(defn truthy [t]
  (truthy* t))

(defrecord Variable [name id constraints]
  Type
  (type [this]
    :variable)
  (truthy* [this]
    (let [instance->val (get-in this [constraints :instance?])]
      instance->val
      (assert false "TODO"))))

(extend-protocol Type
  clojure.lang.IFn
  (tag [this]
    :fn)
  (truthy* [this]
    :true))

(defn variable? [x]
  (instance? Variable x))

(defn get-variable! [env vid]
  {:post [(do (when-not % (println "couldn't find" vid) #p env) true) %]}
  (get-in env [::variables vid]))

(defrecord VariableRef [e id]
  Type
  (type [this]
    :variable)
  (truthy* [this]
    (truthy* (get-variable! e id)))
  (invokeable* [this]
    (assert false "TODO")
    (invokeable* (get-variable! e id))))

(defn variable-ref? [x]
  (instance? VariableRef x))

(s/fdef variable-ref :args (s/cat :e ::env :i nat-int?) :ret variable-ref?)
(defn variable-ref [e id]
  (->VariableRef e id))

(extend-protocol Type
  java.lang.Class
  (type [this]
    :java)
  (truthy* [this]
    (assert false "TODO"))
  (cast* [this type]
    (case type
      :java this
      (assert false "TODO")))
  (valid* [this r]
    (isa? (cast r :java) this))
  (invokeable* [this]
    (instance? clojure.lang.IFn)))

(defn java? [x]
  (instance? Class x))

(defrecord Spec [s]
  Type
  (type [this]
    :spec))

(defn spec? [x]
  (instance? Spec x))

(s/fdef spec :args (s/cat :s s/spec?) :ret spec?)
(defn spec [s]
  (->Spec s))

(defrecord Value [value]
  Type
  (type [this]
    :value)
  (truthy* [this]
    (case (-> value boolean)
      true :true
      false :false)))

(defn value? [x]
  (instance? Value x))

(defn value [x]
  (->Value x))

(defn deref? [x]
  (instance? clojure.lang.IDeref x))

(s/def ::ret type?)
(s/def ::vars (s/map-of var? deref?))

(s/def ::variables (s/map-of integer? variable?))
(s/def ::locals (s/map-of symbol? ::type))

(def vars (atom {}))

(s/def ::env (s/keys :req [::variables ::locals ::ret]))

(s/def ::envs (s/coll-of ::env))

(defn new-env []
  {::variables {}
   ::locals {}
   ::ret (value nil)})

(def ^:dynamic *env* (new-env))

(defn fresh
  ([name]
   (fresh name (swap! type-counter inc)))
  ([name id]
   (->Variable name id {})))

(defn assoc-fresh [env name]
  (let [v (fresh name)
        vid (:id v)]
    [(assoc-in env [:variables vid] v) vid]))

(s/fdef constrain-variable-instance :args (s/cat :e ::env :v nat-int? :c class? :val boolean?) :ret ::env)
(defn constrain-variable-instance [env vid c val]
  (let [vref (get-in env [::variables vid])]
    (assert vref)
    (assert (:id vref)))
  (assoc-in env [::variables vid :contraints :instance? c] val))

(defrecord Env [bindings ret])

(defn type? [x]
  (satisfies? Type x))

(defn predicate-symbol? [x]
  (boolean
   (and (symbol? x)
        (re-find #"\?$" (name x)))))

(defn var-pred? [x]
  (and (var? x)
       (-> x .sym predicate-symbol?)))

(defrecord ErrorT [msg data]
  Type)

(defn error? [x]
  (instance? ErrorT x))

(defn error [msg & [data]]
  (ErrorT. msg data))

(defn a-loc [a]
  (select-keys (:env a) [:file :line :column]))

(defn ns-predicates
  "Return all var predicates in ns"
  [ns]
  (->> ns
       (ns-publics)
       (filter (fn [[sym var]]
                 (predicate-symbol? sym)))
       (vals)))

;; things that appear to be predicates by their name, but aren't
;; because of signature. We can automate this once we infer better


(def not-core-predicates #{#'bound?
                           #'contains?
                           #'distinct?
                           #'empty?
                           #'every?
                           #'even?
                           #'extends?
                           #'future-cancelled?
                           #'future-done?
                           #'identical?
                           #'instance?
                           #'isa?
                           #'neg?
                           #'odd?
                           #'not-any?
                           #'not-every?
                           #'pos?
                           #'realized?
                           #'satisfies?
                           #'some?
                           #'thread-bound?
                           #'zero?})

(defn core-predicates []
  (-> 'clojure.core
      (ns-predicates)
      (set)
      (set/difference not-core-predicates)))

(def pred-gen
  {#'var? (gen/elements (core-predicates))})

(defn get-pred-gen [v]
  (or
   (get @@#'sgen/gen-builtins (deref v))
   (get pred-gen v)
   (assert false (str "no generator for" v))))

(extend-protocol Type
  Var
  (type [this]
    :var-predicate)
  (truthy* [this]
    #p this
    (case this
      #'any? :undecided
      (#'false? #'nil?) :false
      :true))
  (cast* [this tag]
    (println "cast" this "to" tag)
    (assert false))
  (invokeable* [this]
    (instance? clojure.lang.IFn (deref this))))

(defn walk-a-rec
  "Given an analysis a, recursively call (f a path) on all of a's
  `:children`, and also `a` when `path` not provided. Return a seq of
  all `f` return values"
  ([f a]
   (let [path []]
     (concat
      [(f a [])]
      (walk-a-rec f a path))))
  ([f a path]
   (assert a)
   (assert (get-in a path))
   (mapcat (fn [c]
             (if (contains? (get-in a path) c)
               (let [new-path (conj path c)
                     c-node (get-in a new-path)]
                 (if (sequential? c-node)
                   (mapcat (fn [i]
                             (concat [(f a (conj new-path i))] (walk-a-rec f a (conj new-path i)))) (range (count c-node)))
                   (concat [(f a new-path)] (walk-a-rec f a new-path)))))) (get-in a (conj path :children)))))

(defn analyze-cache-a [a]
  (walk-a-rec (fn [a path]
                (let [a* (get-in a path)]
                  (when (= :def (:op a*))
                    (println (:op a*) path "store" (:var a*) (:form a))
                    (data/store-var-analysis (:var a*) a path)))) a))

(defn analyze-cache-ns- [ns]
  (let [env (ana.jvm/empty-env)
        as (analyzer/analyze-ns-1 ns env)]
    (dorun (map analyze-cache-a as))))

(defn analyze-cache-resource [r]
  (->> (analyzer/analyze-resource r (ana.jvm/empty-env))
       (map analyze-cache-a)
       (dorun)))

(s/fdef analyze-ns :args (s/cat :ns namespace?))
(defn analyze-ns [ns]
  (data/mark-ns-analyzed! ns)
  (println "analyzing" ns)
  (binding [*warn-on-reflection* false]
    (analyze-cache-ns- ns)))

(s/fdef ensure-analysis-ns :args (s/cat :ns namespace?))
(defn ensure-analysis [ns]
  (try
    (when-not (data/analyzed-ns? ns)
      (analyze-ns ns))
    (catch Throwable t
      (data/mark-ns-unanalyzed! ns)
      (throw t))))

(s/fdef ensure-analysis-var :args (s/cat :v var?))
(defn ensure-analysis-var [v]
  (ensure-analysis (.ns v)))

(s/fdef get-var-analysis :args (s/cat :v var?))
(defn get-var-analysis [v]
  (ensure-analysis-var v)
  (data/get-var-analysis v))

(defn get-var-analysis-value [v]
  (ensure-analysis-var v)
  (let [{:keys [a path]} (data/get-var-analysis v)
        val (:init a)
        val (if (= :with-meta (:op val))
              (:expr val)
              val)]
    val))

(defn variable? [x]
  (core/instance? Variable x))

(declare valid?)

(s/fdef valid? :args (s/cat :l type? :r type?) :ret boolean?)
(defn valid? [l r]
  (valid* l r))

(defn analyze-form
  "Analyze a form.

   (analyze-form '(string? 3))

   Optionally takes a map of keywordized variables to types:

   (analyze-form '(string? x) {:x #'string?})
  "
  ([form]
   (analyze-form form {}))
  ([form types]
   (let [locals (into {} (map (fn [[binding t]]
                                (let [binding (symbol (name binding))]
                                  [binding {:op :binding
                                            :name binding
                                            :form binding
                                            :env {}
                                            :local :let
                                            ;; :atom (atom {::t (t/new-logic (name binding))})
                                            ::ret-type t
                                            }])) types))]
     (analyzer/analyze form (assoc (ana.jvm/empty-env) :locals locals)))))

(defn compile-dispatch [a]
  ;; (println "compile-dispatch" (:op a))
  (:op a))

(defmulti compile*
  "Takes an analysis. Returns a function [::env -> (coll-of ::env)]"
  #'compile-dispatch)

(defn tracer [f]
  (fn [e]
    (println "calling" (-> f meta (select-keys [:op :var])))
    (validate! ::env e)
    (let [rets (f e)]
      (validate! ::envs rets (meta f))
      ;; (println (-> f meta :op) "returning" (count rets) "envs")
      rets)))

(def compile-memo (memoize compile*))

(defn compile [analysis]
  (println "compile:" (:op analysis) (:form analysis))
  (let [ret (compile-memo analysis)]
    (assert (fn? ret))
    (-> ret
        (with-meta (select-keys analysis [:op :var]))
        (tracer))))

(defn foldl [f coll]
  (println "foldl:" coll)
  (if (seq coll)
    (concat (f (first coll)) (foldl f (rest coll)))
    []))

(defn method-class->t
  "Given an argument or return class from a java method, return a type"
  [c]
  (cond
    (java/primitive? c) c
    :else (assert false "TODO")))

(defn get-java-fn
  "Find and return the type fn that validates a call to this class/method/instance"
  [{:keys [class method instance]}]
  ;; (println "get-java-fn:" class method instance)
  (let [method-arities (java/get-method class method)]
    (fn [& invoke-args]
      #p [:invoke class method :with invoke-args]
      (->> method-arities
           (filter (fn [ar]
                     (if instance
                       (not (contains? (:flags ar) :static))
                       (contains? (:flags ar) :static))))
           (filter (fn [ar]

                     ))
           (map (fn [ar]
                  ;; TODO verify args here
                  ;; when (valid? (cat-t (:parameter-types ar)) (cat-t invoke-args))
                  (java/resolve-java-class (:return-type ar))))
           (filter identity)
           ((fn [rets]
              (if (seq rets)
                (do
                  #p [class method instance rets]
                 (assert false "TODO"))
                (error "no arity of " class method "matches" invoke-args))))))))

(def ^:dynamic *compiling*
  "var -> promise"
  {})

(defn deref-var [v]
  (let [v (get @vars v)]
    (assert v)
    (assert (realized? v))
    @v))

(defmethod compile* :def [a]
  (fn [e]
    (let [v (:var a)
          init-f (promise)]
      (assert (var? v))
      (if (:init a)
        (when (not (get *compiling* v))
          (binding [*compiling* (assoc *compiling* v init-f)]
            (deliver init-f (compile (:init a)))))
        (deliver init-f (fn [e] [(assoc e ::error (error "unbound var" (select-keys a [:var])))])))
      (swap! vars assoc v init-f)
      [(assoc e ::ret v)])))

(defn valid-method?
  "true if this :fn-method analysis can be called with `args`"
  [method args]
  (println "valid-method?" (:form method) args)
  (let [params (:params method)]
    (or (= (count args) (count params))
        (and (:variadic? method) (>= (count args) (count params))))))

(s/fdef bind-params :args (s/cat :e ::env :p (s/coll-of any?) :args (s/coll-of ::type)) :ret ::env)
(defn bind-params
  "Given a call to :fn-method with :params, update `e` to bind args to locals"
  [e params args]
  #p params
  #p args
  (let [p (first params)
        a (if (:variadic? p)
            (rest args)
            (first args))]
    (if (and p a)
      (let [vid (:id a)
            e (if (variable? a)
                (let [e (assoc-in e [::variables vid] a)]
                  (assoc-in e [::locals (:name p)] (variable-ref e vid)))
                (assoc-in e [::locals (:name p)] a))]
        (if (next params)
          (recur e (rest params) (rest args))
          e))
      (throw (ex-info "invalid params:" {:env e :params params :args args})))))

(defmethod compile* :fn-method [a]
  (println "compile :fn-method" (:op (:body a)))
  (let [params (:params a)
        body-f (compile (:body a))]
    (fn [e]
      [(assoc e ::ret (fn [args]
                        {:post [(validate! ::envs %)]}
                        (-> e
                            (bind-params params args)
                            (body-f))))])))

(defmethod compile* :fn [a]
  (println "compile :fn")
  (let [method-table (zipmap (:methods a) (map compile (:methods a)))]
    (fn [e]
      [(assoc e ::ret (fn [args]
                        {:post [(validate! ::envs %)]}
                        (let [methods (->> (filter (fn [[method f]]
                                                     (valid-method? method args)) method-table))]
                          (if (seq methods)
                            (mapcat (fn [[method f]]
                                      (println "running method" (count (:arity method)))
                                      (mapcat (fn [e]
                                                {:post [(validate! ::envs %)]}
                                                ((::ret e) args)) (f e)))
                                    methods)
                            (throw (ex-info "invoke fn no valid method"))))))])))

(defmethod compile* :binding [a]
  (let [init-f (when (:init a) (compile (:init a)))]
    (fn [e]
      (if (:init a)
        (->> (init-f e)
             (mapv (fn [e]
                     (assoc-in e [::locals (:name a)] (::ret e)))))
        [(let [[e vid] (assoc-fresh e (:name a))]
           (assoc-in e [::locals (:name a)] (variable-ref e vid)))]))))

(defmethod compile* :local [a]
  (fn [e]
    (validate! ::env e)
    (let [{:keys [name atom]} a]
      (assert name)
      (let [val (get-in e [::locals (:name a)])]
        (assert (find (::locals e) (:name a)) (print-str "couldn't find" (:name a) "in" e))
        [(assoc e ::ret val)]))))

(defmethod compile* :with-meta [a]
  (println "compile :with-meta" (keys a) (:op (:expr a)))
  (compile (:expr a)))

(defmethod compile* :do [a]
  (validate! map? (:ret a))
  (let [forms (->> (conj (vec (:statements a))
                         (:ret a))
                   (map compile))]
    (fn [e]
      {:pre [(do (validate! ::env e) true)]
       :post [(do (validate! ::envs %) true)]}
      (->> forms
           (reduce (fn [es f]
                     (mapcat f es)) [e])))))

(s/fdef variable-isa? :args (s/cat :e ::env :c class? :v variable-ref?) :ret ::envs)
(defn variable-isa?
  "Truthy if variable has been constrained to (instance? c), or a descendant"
  [e c vref]
  ;; {:post [(do (println "variable-isa?" c vref "=>" (map ::ret %)) true)]}
  (let [vid (:id vref)
        v (get-variable! e vid)]
    (->> (get-in v [:constraints :instance?])
         (filter (fn [[cls val]]
                   (or (when (and val (isa? cls c))
                         [cls (value val)])
                       (when (and (not val) (= cls c))
                         [cls (value val)]))))
         (filter identity)
         first
         ((fn [[cls val]]
            (if cls
              [(assoc e ::ret (value val))]
              (map (fn [val]
                     (-> e
                         (constrain-variable-instance vid c val)
                         (assoc ::ret (value val))))  [true false])))))))

(defmethod compile* :instance? [a]
  (let [{:keys [class target]} a]
    (let [target-f (compile (:target a))]
      (fn [e]
        {:post [(validate! ::envs %)]}
        (->> (target-f e)
             (mapcat (fn [e]
                       (let [t (::ret e)]
                         (cond
                           ;; TODO finish variable constraints
                           (variable-ref? t) (variable-isa? e class t)
                           (instance? t) [(assoc e ::ret (value (isa? (:class t) class)))]
                           :else (assert false (print-str "instance-check:" class t)))))))))))

(defmethod compile* :static-call [a]
  (let [java-f (get-java-fn a)
        arg-fns (map compile (:args a))]
    (fn [e]
      (->> (combo/cartesian-product (map (fn [arg-f]
                                           (arg-f e)) arg-fns))
           (distinct)
           (map (fn [args]
                  (assoc e ::ret (apply java-f args))))))))

(defmethod compile* :instance-call [a]
  (let [java-f (get-java-fn a)
        arg-fns (map compile (:args a))]
    (fn [e]
      (->> (combo/cartesian-product (map (fn [arg-f]
                                           (arg-f e)) arg-fns))
           (distinct)
           (map (fn [args]
                  (assoc e ::ret (apply java-f args))))))))

(defmethod compile* :protocol-invoke [a]
  (fn [e]
    (assoc e ::ret (spec any?))))

(defmethod compile* :the-var [a]
  (fn [e]
    (let [v (get @vars (:var a))]
      (assert v)
      [(assoc e ::ret v)])))

(s/fdef compile-var :args (s/cat :e ::env :v var?))
(defn compile-var [e v]
  {:pre [(do (println "compile-var pre" v ) true)]
   :post [(do (println "compile-var:" v) true) (get @vars v)]}
  (ensure-analysis-var v)
  (let [{:keys [a path]} (data/get-var-analysis v)]
    (assert a (pr-str "couldn't find analysis for" v))
    #p (:op a)
    (let [es ((compile a) e)
          e (first! es)]
      (validate! ::env e))))

(s/fdef ensure-var-compilation :args (s/cat :e ::env :v var?))
(defn ensure-var-compilation [e v]
  (or (when (get @vars v)
        e)
      (compile-var e v)))

(defn get-var
  [v]
  (let [var-promise (get @vars v)]
    (assert var-promise)
    (assert (realized? var-promise))
    @var-promise))

(s/fdef invokeable? :args (s/cat :t type?) :ret boolean?)
(defn invokeable? [t]
  (invokeable* t))

(defn invoke [e f args]
  (cond
    (var? f) (-> ((get-var f) e) first! ::ret (.invoke args))
    :else (assert false)))

(defn evaluate
  "Given a seq of envs and a seq of compiled env fns, evaluate"
  [es fs]
  )

(defmethod compile* :invoke [a]
  (assert (every? :op (:args a)))
  (let [f-fn (compile (:fn a))
        arg-fns (map compile (:args a))]
    (fn [e]
      (println ":invoke" (:fn a) (:op (:fn a)))
      (let [es-s (reduce (fn [es-s f]
                           {:post [(validate! (s/coll-of ::envs) %)]}
                           (assert (ifn? f))
                           (conj (vec es-s) (mapcat (fn [e]
                                                      (if (not (::error e))
                                                        (f e)
                                                        [e])) (last es-s)))) [(f-fn e)] arg-fns)]

        (assert (= (count es-s)) (inc (count (:args a))))
        (validate! (s/coll-of ::envs) es-s)
        (->> (apply combo/cartesian-product es-s)
             (mapcat (fn [es]
                       (assert (= (count es) (inc (count (:args a))) ))
                       (let [[f & args] (map ::ret es)
                             e (last es)]
                         (if (invokeable? f)
                           (invoke e f args)
                           [(assoc e ::error (error (print-str "can't invoke" f)))])))))))))

(defmethod compile* :let [a]
  (println "compile :let" (:form a))
  (let [fs (conj (mapv compile (:bindings a))
                 (compile (:body a)))]
    (fn [e]
      {:post [(validate! ::envs %)]}
      (reduce (fn [es f]
                (mapcat f es)) [e] fs))))

(defmethod compile* :if [a]
  (let [test-f (compile (:test a))
        then-f (compile (:then a))
        else-f (compile (:else a))]
    (fn [e]
      {:post [(validate! (s/coll-of ::env) %)]}
      (->> (test-f e)
           (mapcat (fn [e]
                     (case (truthy (::ret e))
                       :true (then-f e)
                       :false (else-f e)
                       :undecided (concat (then-f e) (else-f e)))))))))

(defmethod compile* :const [a]
  (fn [e]
    {:pre [(do (validate! ::env e) true)]
     :post [(do (validate! ::envs %) true)]}
    [(assoc e ::ret (value (:val a)))]))

(defmethod compile* :recur [a]
  (fn [e]
    [e]))

(defmethod compile* :var [a]
  (fn [e]
    [(-> (ensure-var-compilation e (:var a))
         (assoc ::ret (:var a)))]))

(defn compile-constructor
  "returns a spectrum function for invoking the constructor"
  [constructor]
  (let [constructor-args (map java/resolve-java-class (:parameter-types constructor))]
    (fn [e]
      (fn [& args]
        (if (= (count constructor-args) (count args))
          (->
           (reduce (fn [e [constructor-arg arg]]
                     (if (not (:error e))
                       (if (valid? #p constructor-arg #p arg)
                         e
                         (assoc e ::error (error (print-str "can't pass" arg "to" constructor-arg))))
                       e)) e (zipmap constructor-args args))
           ((fn [e]
              (if (not (:error e))
                (assoc e ::ret (-> constructor :name java/resolve-java-class))
                e))))
          [(assoc e ::error (error (print-str "Invalid constructor arity: expected" (count constructor-args) "got" (count args))))])))))

(defmethod compile* :new [a]
  (let [class-f (compile (:class a))
        args-fns (map compile (:args a))]
    (fn [e]
      (if (not (:error e))
        (for [e (class-f e)
              :let [cls (-> e ::ret)
                    _ (assert (value? cls))
                    cls (-> cls :value)]
              args (->> args-fns
                        (map (fn [arg-f]
                               (validate! ::envs (arg-f e))))
                        (combo/cartesian-product)
                        (distinct))
              :let [constructors (java/get-constructors cls (count args))]]
          (if (seq constructors)
            (mapcat (fn [constructor]
                      (-> (compile-constructor constructor)
                          (.invoke e)
                          (.invoke args))) constructors)
            [(assoc e ::error (error "can't construct" a))]))
        [e]))))

(defmethod compile* :throw [a]
  (let [ex-f (compile (:exception a))]
    (fn [e]
      (->> (ex-f e)
           (map (fn [e]
                  (if (valid? Throwable (::ret e))
                    e
                    (assoc e ::error (error "can't throw non-throwable" (::ret e))))))))))

(defn get-fn-method-by-arity
  "given an :fn analysis, return the :fn-method for arity n"
  [fa arity]
  (assert (= :fn (:op fa)))
  (->> fa
       :methods
       (filter (fn [meth]
                 (or (= arity (:fixed-arity meth))
                     (and (:variadic? meth)
                          (>= arity (:fixed-arity meth))))))
         first))

(defn compile-form [form]
  (compile (analyze-form form)))

(s/fdef test-invoke :args (s/cat :v var? :args (s/coll-of type?)))
(defn test-invoke
  "returns the result of invoking var with args"
  [v args]
  (let [e *env*
        e (ensure-var-compilation *env* v)]
    (alter-var-root #'*env* (constantly e))
    (binding [*env* e]
      (if-let [f (get-var v)]
        (let [es (f *env*) ;; init-f
              ]
          (-> es
              first!
              ::ret
              (.invoke args)))

        (throw (ex-info (print-str "couldn't find var" v) *env*)))))
  )

(defn check-compiled-fn
  "Takes a compiled fn, and checks it"
  [f]
  (->> (-> f meta :arities)
       (mapv (fn [a]
               (let [args (mapv (fn [i]
                                 (fresh (str "a" i))) (range (-> a :arg-count)))
                     ret (apply f args)]
                 {:args args
                  :ret ret})))))

(defn sat? [envs]
  (every? (fn [e] (not (:error e))) envs))

(instrument-ns)

;; nil and primitives and arrays aren't objects, but they are `any?`
;; therefore any is the root
;; (derive-type #'any? Object)

;; (derive-type #'any? #'bytes?)
;; (derive-type #'any? #'char?)
;; (derive-type #'any? #'nil?)
;; (derive-type #'any? #'number?)
;; (derive-type #'number? #'int?)
;; (derive-type #'number? #'integer?)
;; (derive-type (or-t [#'keyword? #'symbol?]) #'ident?)
;; (derive-type #'ident? #'simple-ident?)
;; (derive-type #'keyword? #'simple-keyword?)
;; (derive-type #'keyword? #'qualified-keyword?)
;; (derive-type BigDecimal #'decimal?)
;; (derive-type Boolean #'boolean?)
;; (derive-type Boolean #'false?)
;; (derive-type Boolean #'true?)
;; (derive-type Character #'char?)
;; (derive-type Class #'class?)
;; (derive-type Double #'double?)
;; (derive-type Double #'float?)
;; (derive-type Float #'float?)
;; (derive-type Keyword #'keyword?)
;; (derive-type Number #'number?)
;; (derive-type clojure.lang.Associative #'associative?)
;; (derive-type clojure.lang.Counted #'counted?)
;; (derive-type clojure.lang.Delay #'delay?)
;; (derive-type clojure.lang.Fn #'fn?)
;; (derive-type clojure.lang.IChunkedSeq #'chunked-seq?)
;; (derive-type clojure.lang.IFn #'ifn?)
;; (derive-type clojure.lang.IPersistentCollection #'coll?)
;; (derive-type clojure.lang.IPersistentMap #'map?)
;; (derive-type java.util.concurrent.Future #'future?)

nil
