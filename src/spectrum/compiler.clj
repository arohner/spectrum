(ns spectrum.compiler
  (:refer-clojure :exclude [ancestors compile descendants type instance?])
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
            [spectrum.util :refer [instrument-ns validate! namespace? atom? !]])
  (:import [clojure.lang Symbol Keyword Var IPersistentMap]))

(def types-hierarchy (atom (make-hierarchy)))

(def type-counter (atom 0))

(defprotocol Type
  (tag [this]
    "Return a tag corresponding to the type of this instance. Must be
    something `valid-dispatch` knows how to handle")
  (truthy [this]
    "Return :true :false or :undecided if this type appears in the
    test of an `if`"))

(defn type? [x]
  (satisfies? Type x))

(defprotocol InvokeType
  "Represents invokable things"
  :extend-via-metadata true
  (form [this]
    "Return a map of input types to output types"))

(defrecord Variable [name id constraints]
  ;; (tag [this]
  ;;   :variable)
  )

(defn variable? [x]
  (core/instance? Variable x))

(defrecord VariableRef [id]
  Type
  (tag [this]
    :variable))

(defn vref? [x]
  (core/instance? VariableRef x))

(s/fdef vref :args (s/cat :i nat-int?) :ret vref?)
(defn vref [id]
  (->VariableRef id))

(defrecord Instance [class]
  Type
  (tag [this]
    :instance))

(defn instance? [x]
  (core/instance? Instance x))

(s/fdef instance :args (s/cat :c class?) :ret instance?)
(defn instance [cls]
  (->Instance cls))

(defrecord Spec [s]
  Type
  (tag [this]
    :spec))

(defn spec? [x]
  (core/instance? Spec x))

(s/fdef spec :args (s/cat :s s/spec?) :ret spec?)
(defn spec [s]
  (->Spec s))

(defrecord Value [v]
  Type
  (tag [this]
    :value))

(defn value? [x]
  (instance? Value x))

(defn value [x]
  (->Value x))

(def ^:dynamic *env* {})
(s/def ::ret any?)
(s/def ::vars (s/map-of var? fn?))
(s/def ::vars (s/map-of symbol? fn?))

(s/def ::variables (s/map-of integer? variable?))
(s/def ::locals (s/map-of symbol? type?))

(s/def ::env (s/keys :opt [::vars ::variables ::locals ::ret]))

(s/def ::envs (s/coll-of ::env))

(defn get-variable! [env vid]
  {:post [%]}
  (get-in env [:variables vid]))

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
  (assert (get-in env [:variables vid]))
  (assoc-in env [:variables (:id vref) :contraints :instance? c] val))

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

(defn ancestors [t]
  (core/ancestors @types-hierarchy t))

(defn sorted-ancestors
  "Returns ancestors of t, sorted such that later entries are either peers or descendants of earlier entries"
  [t])

(defn descendants [t]
  (core/descendants @types-hierarchy t))

;; (defn derive-type
;;   "clojure.core/derive, but patched to allow types.

;; Note arguments are reversed from clojure.core/derive, to resemble (valid? x y)"
;;   ([h parent type]
;;    (assert (not= type parent) (format "derive-type: can't derive %s -> %s" parent type))
;;    (assert h)
;;    (assert (type? parent))
;;    (assert (type? type))
;;    (let [tp (:parents h)
;;          td (:descendants h)
;;          ta (:ancestors h)
;;          tf (fn [m source sources target targets]
;;               (reduce (fn [ret k]
;;                         (assoc ret k
;;                                (reduce conj (get targets k #{}) (cons target (targets target)))))
;;                       m (cons source (sources source))))]
;;      (when-not tp
;;        (println "derive-type:" parent type "no parents"))
;;      (assert tp)
;;      (assert ta)
;;      (assert td)
;;      (assert tf)
;;      (when-not (contains? (tp type) parent)
;;        (when (contains? (ta type) parent)
;;          (throw (Exception. (print-str type "already has" parent "as ancestor"))))
;;        (when (contains? (ta parent) type)
;;          (throw (Exception. (print-str "Cyclic derivation:" parent "has" type "as ancestor"))))
;;        {:parents (assoc (:parents h) type (conj (get tp type #{}) parent))
;;         :ancestors (tf (:ancestors h) type td parent ta)
;;         :descendants (tf (:descendants h) parent ta type td)})))
;;   ([parent type]
;;    ;; (ensure-type-any parent)
;;    ;; (ensure-type-any type)
;;    (let [ret (derive-type @types-hierarchy parent type)]
;;      (when ret
;;        (reset! types-hierarchy ret)))))

(defrecord ErrorT [msg]
  Type)

(defn error? [x]
  (instance? ErrorT x))

(defn error [msg]
  (ErrorT. msg))

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
  (tag [this]
    :var-predicate)
  (spec [this]
    (s/with-gen (s/spec (deref this))
      (fn []
        (get-pred-gen this)))))

(def class-gen
  "Map of class to spec generator"
  {Boolean (gen/elements [true false])
   Object (gen/elements [(Object.) (Object.) (Object.)])
   Integer (gen/fmap (fn [i]
                       (Integer. i)) (s/gen (s/int-in Integer/MIN_VALUE Integer/MAX_VALUE)))

   Long (gen/fmap (fn [i]
                    (Long. i)) (s/gen (s/int-in Long/MIN_VALUE Long/MAX_VALUE)))
   Keyword (s/gen keyword?)
   String (s/gen string?)})

(defn solve-contraints [cs])

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

(deftype Cat [ts]
  Type
  (tag [this]
    :regex))

(defn cat-t [ts]
  (->Cat ts))

(deftype Or [ts]
  Type
  (tag [this]
    :or))

(defmethod print-method Or [this ^java.io.Writer w]
  (.write w "#spectrum.compiler/Or ")
  (print-method (.ts this) w))

(defn or? [x]
  (core/instance? Or x))

(s/fdef or-consolidate :args (s/cat :ts (s/coll-of type?)))
(defn or-consolidate [ts]
  (let [ors (filter or? ts)
        non-ors (remove or? ts)]
    (set/union (set non-ors) (set (mapcat #(.ts %) ors)))))

(s/fdef or-t :args (s/cat :ts (s/coll-of type?)) :ret type?)
(defn or-t [ts]
  (let [ts (or-consolidate ts)]
    (case (count ts)
      1 (first ts)
      0 (error "")
      (->Or ts))))

(deftype And [ts]
  Type
  (tag [this]
    :and))

(deftype Amb [ts]
  Type
  (tag [this]
    :amb))

(defn and-t [& ts]
  (->And (set ts)))

(defn amb-t [& ts]
  (->Amb (distinct ts)))

(declare valid?)

(defn valid-and-and [l r]
  (assert false "TODO"))

(defn valid-and-or [l r]
  (assert false "TODO"))

(defn valid-or-and [l r]
  (assert false "TODO"))

(defn valid-or-or [l r]
  (assert false "TODO"))

(defn valid-or-any [l r]
  (assert false "TODO"))

(defn valid-variable-variable [l r]
  (assert false "TODO"))

(defn valid-variable-any [l r]
  (assert false "TODO"))

(defn valid-and-any [l r]
  (assert false "TODO"))

(defn valid-any-and [l r]
  (some (fn [r*]
          (valid? l r*)) (.ts r)))

(defn valid-any-or [l r]
  (every? (fn [r*]
            (valid? l r*)) (.ts r)))

(defn valid-variable-variable [l r]
  (swap! (.constraints l) conj [:< l r])
  (swap! (.constraints r) conj [:< l r]))

(defn valid-any-variable [l r]
  (assert (not (variable? l)))
  (swap! (.constraints r) conj [:< l r]))

(defn valid-variable-any [l r]
  (assert (not (variable? r)))
  (swap! (.constraints l) conj [:< l r]))

(defn valid-variable-variable [l r]
  (swap! (.constraints l) conj [:< l r]))

(defn valid-var-any [l r]
  (or (= l #'any?)
      (= l r)
      (contains? (ancestors r) l)))

(defn valid-class-any [l r]
  (->> r
       ancestors
       (filter (fn [t]
                 (= :class t)))
       (some (fn [t]
               (valid? l t)))))

(defn valid-class-class [l r]
  (isa? r l))

(defn different-ancestors [t]
  (->> (ancestors t)
       (filter (fn [t*]
                 (not= (tag t) (tag t*))))))

(defn valid-regex-regex [l r]
  (assert false "TODO"))

(defn valid-dispatch [l r]
  {:post [(do (println "valid-dispatch:" l r "=>" %) true)]}
  (let [tl (tag l)
        tr (tag r)]
    (case [tl tr]
      [:or :and] valid-or-and
      [:or :or] valid-or-or
      [:and :and] valid-and-and
      [:variable :variable] valid-variable-variable
      [:class :class] valid-class-class
      [:regex :regex] valid-regex-regex
      (case tr
        :or valid-any-or
        :and valid-any-and
        :variable valid-any-variable
        (case tl
          :and valid-and-any
          :or valid-or-any
          :variable valid-variable-any
          :class valid-class-any
          :var-predicate valid-var-any)))))

(s/fdef valid? :args (s/cat :l type? :r type?) :ret boolean?)
(defn valid? [l r]
  (boolean
   (some (fn [r*]
           ((valid-dispatch l r*) l r*)) (lazy-cat [r] (different-ancestors r)))))

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
    (println "calling" (-> f meta :op))
    (let [rets (f e)]
      (validate! ::envs rets)
      (println (-> f meta :op) "ret" (count rets))
      rets)))

(defn compile [analysis]
  (println "compile:" (:op analysis))
  (let [ret (compile* analysis)]
    (assert (fn? ret))
    (-> ret
        (with-meta (select-keys analysis [:op]))
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
    :else (or-t [c #'nil?])))

(defn get-java-fn
  "Find and return the type fn that validates a call to this class/method/instance"
  [{:keys [class method instance]}]
  ;; (println "get-java-fn:" class method instance)
  (let [method-arities (java/get-method class method)]
    (fn [& invoke-args]
      (->> method-arities
           (filter (fn [ar]
                     (if instance
                       (not (contains? (:flags ar) :static))
                       (contains? (:flags ar) :static))))
           (map (fn [ar]
                  ;; TODO verify args here
                  ;; when (valid? (cat-t (:parameter-types ar)) (cat-t invoke-args))
                  (method-class->t (java/resolve-java-class (:return-type ar)))))
           (filter identity)
           ((fn [rets]
              (if (seq rets)
                (or-t rets)
                (error "no arity of " class method "matches" invoke-args))))))))

(defmethod compile* :def [a]
  (let [init-f (compile (:init a))
        v (:var a)]
    (fn [e]
      [(-> e
           (assoc-in [:vars v] init-f)
           (assoc ::ret v))])))

(defn valid-method?
  "true if this :fn-method analysis can be called with `args`"
  [method args]
  (println "valid-method?" (:form method) args)
  (let [params (:params method)]
    (or (= (count args) (count params))
        (and (:variadic? method) (>= (count args) (count params))))))

(defn bind-params
  "Given a call to :fn-method with :params, update `e` to bind args to locals"
  [e params args]
  (let [p (first params)
        a (if (:variadic? p)
            (rest args)
            (first args))]
    (if (and p a)
      (let [vid (:id a)
            e (if (variable? a)
                (-> e
                    (assoc-in [:variables vid] a)
                    (assoc-in [:locals (:name p)] (vref vid)))
                (assoc-in e [:locals (:name p)] a))]
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
                        (-> e
                            (bind-params params args)
                            (body-f))))])))

(defmethod compile* :fn [a]
  (println "compile :fn")
  (let [method-table (zipmap (:methods a) (map compile (:methods a)))]
    (fn [e]
      [(assoc e ::ret (fn [args]
                        (let [methods (->> (filter (fn [[method f]]
                                                     (valid-method? method args)) method-table))]
                          (if (seq methods)
                            (mapcat (fn [[method f]]
                                      (println "running method" (count (:arity method)))
                                      (map (fn [e]
                                             (-> e ::ret (.invoke args))) (f e)))
                                    methods)
                            (throw (ex-info "invoke fn no valid method"))))))])))

(defmethod compile* :binding [a]
  (let [init-f (when (:init a) (compile (:init a)))]
    (fn [e]
      (if (:init a)
        (->> (init-f e)
             (mapv (fn [e]
                     (assoc-in e [:locals (:name a)] (::ret e)))))
        [(let [[e vid] (assoc-fresh e (:name a))]
           (assoc-in e [:locals (:name a)] (vref vid)))]))))

(defmethod compile* :local [a]
  (fn [e]
    (validate! ::env e)
    (let [{:keys [name atom]} a]
      (assert name)
      (let [val (get-in e [:locals (:name a)])]
        (assert (find (:locals e) (:name a)) (print-str "couldn't find" (:name a) "in" e))
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

(s/fdef variable-isa? :args (s/cat :e ::env :c class? :v vref?) :ret (s/coll-of ::env))
(defn variable-isa?
  "Truthy if variable has been constrained to (instance? c), or a descendant"
  [e c vref]
  (let [vid (:id vref)
        v (get-variable! e vid)]
    (->> (get-in v [:constraints :instance?])
         (filter (fn [[cls val]]
                   (or (when (and val (isa? cls c))
                         [cls val])
                       (when (and (not val) (= cls c))
                         [cls val]))))
         (filter identity)
         first
         ((fn [[cls val]]
            (if cls
              (assoc e ::ret val)
              (map (fn [val]
                     (-> e
                         (assoc ::ret val)
                         (constrain-variable-instance vid c val)))  [true false])))))))

(defn instance-check? [class t]
  (cond
    (variable? t) (variable-isa? class t)
    (instance? t) (isa? (:class t) class)
    :else (assert false (print-str "instance-check:" class t))))

(defmethod compile* :instance? [a]
  (let [{:keys [class target]} a]
    (let [target-f (compile (:target a))]
      (fn [e]
        {:post [(validate! (s/coll-of ::env) %)]}
        (->> (target-f e)
             (mapcat (fn [e]
                       (let [t (::ret e)]
                         (cond
                           ;; TODO finish variable constraints
                           (vref? t) (variable-isa? e class t)
                           (instance? t) [(assoc e ::ret (isa? (:class t) class))]
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
    (let [v (get-in e [:vars (:va a)])]
      (assert v)
      [(assoc e ::ret v)])))

(s/fdef compile-var :args (s/cat :v var?))
(defn compile-var [v]
  (ensure-analysis-var v)
  (let [{:keys [a path]} (data/get-var-analysis v)]
    (assert a (pr-str "couldn't find analysis for" v))
    (let [es ((compile a) *env*)
          _ (assert (= 1 (count es)) (print-str "expected 1, got" (count es)))
          e (first es)]

      (validate! ::env e)
      (alter-var-root #'*env* (constantly e)))))

(s/fdef ensure-var-compilation :args (s/cat :v var?))
(defn ensure-var-compilation [v]
  (or (get-in *env* [:vars v])
      (compile-var v)))

(defn get-var [v]
  (get-in *env* [:vars v]))

(defmethod compile* :invoke [a]
  (fn [e]
    (println "invoke!")
    [e])
  ;; (let [arg-fns (map (fn [a]
  ;;                      (compile* a)) (:args a))]
  ;;   (case (:op (:fn a))
  ;;     :var (let [v (-> a :fn :var)]
  ;;            (ensure-var-compilation v)
  ;;            (fn [e]
  ;;              (let [f (get-in env [:vars v])
  ;;                    _ (assert f (pr-str "couldn't find compilation for" v))]
  ;;                (->> (combo/cartesian-product (map (fn [a-f] (a-f e)) arg-fns))
  ;;                     (map (fn [args]
  ;;                            (assoc e ::ret (apply f e args))))))))))
  )

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
      {:post [ (validate! (s/coll-of ::env) %)]}
      (->> (test-f e)
           (mapcat (fn [e]
                     (if (::ret e)
                       (then-f e)
                       (else-f e))))))))

(defmethod compile* :const [a]
  (fn [e]
    {:pre [(do (validate! ::env e) true)]
     :post [(do (validate! ::envs %) true)]}
    [(assoc e ::ret (:val a))]))

(defmethod compile* :recur [a]
  (assert false))

(defmethod compile* :new [a]
  (let [class-f (compile (:class a))]
    (fn [e]
      #p (:class a)
      (->> (class-f e)
           (map (fn [e]
                  (assoc e ::ret (instance (::ret e)))))))))

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
  (ensure-var-compilation v)
  (assert *env*)
  (if-let [f (get-in *env* [:vars v])]
    (let [es (f *env*) ;; deref var
          _ (assert (= 1 (count es)))
          e (first es)]
      (-> e
          ::ret
          (.invoke args)))

    (throw (ex-info (print-str "couldn't find var" v) *env*))))

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
