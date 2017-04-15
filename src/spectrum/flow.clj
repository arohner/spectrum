(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.string :as str]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.java :as j]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)])
  (:import clojure.lang.Var))

(declare recur?)
(declare find-binding)

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(defrecord RecurForm [args]
  c/Spect
  (conform* [this x]
    false))

(defrecord ThrowForm [exception-class]
  c/Spect
  (conform* [this x]
    false))

(s/fdef recur? :args (s/cat :x any?) :ret boolean?)
(defn recur? [x]
  (instance? RecurForm x))

(defn recur-form [args]
  (map->RecurForm {:args args}))

(s/fdef throwable? :args (s/cat :x any?) :ret boolean?)
(defn throwable? [x]
  (instance? Throwable x))

(s/fdef throw? :args (s/cat :x any?) :ret boolean?)
(defn throw? [x]
  (instance? ThrowForm x))

(s/fdef throw-form :args (s/cat :e class?) :ret throw?)
(defn throw-form [e]
  (map->ThrowForm {:exception-class e}))

(s/fdef control-flow? :args (s/cat :x any?) :ret boolean?)
(defn control-flow? [x]
  (or (throw? x) (recur? x)))

(defn spect-or-control-flow? [x]
  (or (c/spect? x) (control-flow? x)))

(s/def ::args-spec ::c/spect-like)
(s/def ::ret-spec ::c/spect-like)

(s/def ::var (s/with-gen (s/spec var?)
               (fn []
                 (gen/elements [#'int? #'println #'str]))))

(s/def ::analysis (s/merge ::ana.jvm/analysis (s/keys :opt [::var ::args-spec ::ret-spec])))

(s/def ::analysis? (s/nilable ::analysis))

(s/def ::analyses (s/coll-of ::analysis))

(s/fdef a-loc :args (s/cat :a ::ana.jvm/analysis))
(defn a-loc [a]
  (select-keys a [:file :line :column]))

(defn a-loc-str
  "A human-formatted string for the file & line of the current analysis"
  [a]
  (let [{{:keys [file line column]} :env} a]
    (str "file " file " line " line " col " column)))

(s/fdef flow-dispatch :args (s/cat :a ::ana.jvm/analysis) :ret keyword?)
(defn flow-dispatch [a]
  (assert (:op a))
  (:op a))

(s/fdef flow :args (s/cat :a ::ana.jvm/analysis) :ret ::analysis)

(defmulti flow
  "Given an analysis, walk and update-in the the analysis attaching ::args-spec and ::ret-spec to values"
  #'flow-dispatch)

(s/fdef flow-ns :args (s/cat :as ::analyses) :ret ::analyses)

(defn flow-ns
  "Given the result of analyze-ns, flow all forms"
  [as]
  (mapv flow as))

(defn java-type->spec [t]
  (c/class-spec
   (cond
     (j/primitive? t) (j/primitive->class t)
     (symbol? t) (j/resolve-class t)
     (class? t) t
     :else (assert "unknown type:" t))))

(s/fdef maybe-assoc-var-name :args (s/cat :a ::analysis) :ret ::analysis)
(defn maybe-assoc-var-name
  "Given a def analysis, if the def stores a fn, update the :fn analysis to contain the varname, for future analysis"
  [a]
  (let [path (if (-> a :init :op (= :with-meta))
               [:init :expr]
               [:init])]
    (if (= :fn (:op (get-in a path)))
      (assoc-in a (conj path ::var) (:var a))
      a)))

(defn invoke-predicate?
  "True if the analysis is invoking a predicate"
  [a]
  (and (-> a :op (= :invoke))
       (-> a :fn :op (= :var))
       (-> a :args count (= 1))
       (some-> a :fn :var c/var-predicate?)))

(defn invoke-nil?
  "True if the analysis is invoking the inlined version of #'nil?, which is a :static-call to clojure.lang.Util/identical"
  [a]
  (and (-> a :op (= :static-call))
       (-> a :class (= clojure.lang.Util))
       (-> a :method (= 'identical))
       (-> a :args (nth 1) :val (= nil))))

(def variable-bindings
  "The set of analyzer ops that are derefing a variable"
  #{:local :var})

(defn invoke-truthy?
  "Truth if the analysis is just a simple 'foo, like (if foo...)"
  [a]
  (contains? variable-bindings (:op a)))

;; TODO should be (s/fspec :args (s/cat :a ::ana.jvm/analysis) :ret ::analysis), need analysis gen

(s/fdef walk-a :args (s/cat :f fn? :a ::ana.jvm/analysis) :ret ::analysis)
(defn walk-a
  "Walk and update an analysis."
  [f a]
  (reduce (fn [a c]
            (if (contains? a c)
              (update-in a [c] (fn [c-node]
                                 (if (sequential? c-node)
                                   (mapv (fn [n]
                                           (f (with-a n a))) c-node)
                                   (f (with-a c-node a)))))
              a)) a (:children a)))

(defn flow-walk [a]
  (try
    (binding [*a* a]
      (walk-a flow a))
    (catch Throwable t
      (println "flow-walk exception while walking:" (a-loc-str a) (:form a))
      (throw t))))

(defmethod flow :default [a]
  {:post [(c/spect? (::ret-spec %))]}
  (flow-walk a))

(defmethod flow :quote [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :expr ::ret-spec))))

(defmethod flow :def [a]
  {:post [(c/spect? (::ret-spec %))]}
  (data/store-var-analysis a)
  (let [a (maybe-assoc-var-name a)
        a (flow-walk a)]
    (assoc a ::ret-spec (c/pred-spec #'var?))))

(defmethod flow :the-var [a]
  {:post [(c/spect? (::ret-spec %))]}
  ;; the-var => (var foo). Returns the actual var
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/value (:var a)))))

(defmethod flow :var [a]
  {:post [(c/spect? (::ret-spec %))]}
  ;; :var => the value the var holds
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (if-let [s (c/get-var-fn-spec (:var a))]
                          s
                          (c/value @(:var a))))))

(defmethod flow :with-meta [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (::ret-spec (:expr a)))))

(defmethod flow :fn [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/parse-spec (s/and fn? ifn?)))))

(defn find-binding*-dispatch [a name]
  (:op a))

(defmulti find-binding* #'find-binding*-dispatch)

(defn find-binding-default [a name]
  (when-let [b (get-in a [:env :locals name])]
    (when (::ret-spec b)
      b)))

(defmethod find-binding* :default [a name]
  (find-binding-default a name))

(defmethod find-binding* :let [a name]
  (->> a
       :bindings
       (filter (fn [b] (= name (:name b))))
       first))

(defmethod find-binding* :loop [a name]
  (->> a
       :bindings
       (filter (fn [b] (= name (:name b))))
       first))

(defmethod find-binding* :binding [a name]
  (when (= name (:name a))
    a))

(defn find-binding-method [a name]
  (->> a
       :params
       (filter (fn [b] (= name (:name b))))
       first))

(defmethod find-binding* :fn-method [a name]
  (find-binding-method a name))

(defmethod find-binding* :fn [a name]
  (when (-> a :local :name (= name))
    (:local a)))

(defmethod find-binding* :method [a name]
  (or (find-binding-method a name)
      (when (= name (-> a :this :name))
        (:this a))))

(defmethod find-binding* :deftype [a name]
  (->> a
       :fields
       (filter (fn [b] (= name (:name b))))
       first))

(defmethod find-binding* :catch [a name]
  (when (-> a :local :name (= name))
    (:local a)))

(s/fdef maybe-disj-pred :args (s/cat ::s ::c/spect :p ::c/spect) :ret ::c/spect)
(defn maybe-disj-pred
  "If s is an or-spec, remove p if present"
  [s p]
  {:post [(do (when-not (s/valid? ::c/spect %)
             (println "maybe-disj-pred:" s p "=>" %)) true) (s/valid? ::c/spect %)]}
  (if (c/or-spec? s)
    (c/or-disj s p)
    s))

(defn maybe-disj-truthy
  "If s is an or-spec remove all unambiguously truthy specs, because this just failed an `if"
  [s]
  (if (c/or-spec? s)
    (c/filter* (fn [p]
                 (not= :truthy (c/truthyness p))) s)
    s))

(defn binding-update-if-specs
  "Given a :binding, walk up the tree to find all :if predicate tests it contains, and update the spec"
  [a binding]
  (loop [a a
         spec (::ret-spec binding)]
    (assert spec)
    (if a
      (let [parent (unwrap-a a)]
        (if (= :if (:op parent))
          (let [{:keys [test then else]} parent
                this-expr (cond
                            (and (= (:form a) (:form test)) (= (a-loc a) (a-loc test))) :test
                            (and (= (:form a) (:form then)) (= (a-loc a) (a-loc then))) :then
                            (and (= (:form a) (:form else)) (= (a-loc a) (a-loc else))) :else
                            :else (do
                                    (assert false)))
                this (get parent this-expr)
                test-type (cond
                            (invoke-predicate? test) :pred
                            (invoke-nil? test) :nil
                            (invoke-truthy? test) :truthy
                            (= :instance? (:op test)) :instance?
                            :else nil)]
            (if (and test-type
                     (or (-> test :form (= (:form binding)))
                         (-> test :args first :name (= (:name binding)))
                         (-> test :target :name (= (:name binding)))))
              (let [test-pred (cond
                                (invoke-predicate? test) (c/pred-spec (-> test :fn :var))
                                (invoke-nil? test) (c/pred-spec #'nil?))
                    updated-spec-then (condp = test-type
                                        :pred (c/and-spec [spec test-pred])
                                        :nil (c/and-spec [spec test-pred])
                                        :truthy (-> spec (maybe-disj-pred (c/pred-spec #'nil?)) (maybe-disj-pred (c/pred-spec #'false?)))
                                        :instance? (c/and-spec [spec (c/class-spec (:class test))]))
                    updated-spec-else (condp = test-type
                                        :pred (maybe-disj-pred spec test-pred)
                                        :nil (maybe-disj-pred spec test-pred)
                                        :truthy (maybe-disj-truthy spec)
                                        :instance? spec ;; todo not class-spec
                                        )]
                (cond
                  (= this-expr :then) (recur parent updated-spec-then)
                  (= this-expr :else) (recur parent updated-spec-else)
                  :else (recur parent spec)))
              (recur parent spec)))
          (recur parent spec)))
      (assoc binding ::ret-spec spec))))

(s/fdef find-binding :args (s/cat :a ::analysis :name symbol?) :ret (s/nilable ::analysis))
(defn find-binding
  "recursively unwrap a, looking for a :binding for 'name"
  [a name]
  {:post [(s/valid? (s/nilable ::analysis) %)]}
  (loop [a* a]
    (when a*
      (if-let [b (find-binding* a* name)]
        (binding-update-if-specs a b)
        (when-let [a* (unwrap-a a*)]
          (recur a*))))))

(s/fdef analysis-args->spec :args (s/cat :a ::ana.jvm/analyses) :ret ::c/spect)
(defn analysis-args->spec
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/map->RegexCat {:ps (mapv (fn [arg]
                                (when-not (::ret-spec arg)
                                  (println "analysis-args->spec:" arg (:form arg)))
                                (assert (::ret-spec arg))
                                (c/maybe-spec-spec (::ret-spec arg))) args)
                    :ret []}))

(s/fdef maybe-strip-meta :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)
(defn maybe-strip-meta
  "If a is a :op :with-meta, strip it and return the :expr, or a"
  [a]
  (if (-> a :op (= :with-meta))
    (-> a :expr)
    a))

(s/fdef invoke-valid-arity? :args (s/cat :f ::analysis :arg-count integer?) :ret boolean?)
(defn invoke-valid-arity?
  "check the fn invoke for correct arity. Takes the :fn analysis, and the caller args"
  [a arg-count]
  (assert (= :fn (:op a)))
  (let [args (:args a)]
    (boolean (some (fn [m]
                     (or (and (not (:variadic? m))
                              (= arg-count (:fixed-arity m)))
                         (and (:variadic? m)
                              (>= arg-count (:fixed-arity m))))) (-> a :methods)))))

(defn get-var-fn-analysis [a]
  (some-> a :init maybe-strip-meta))

(defn invoke-get-fn-analysis [a]
  (assert (= :invoke (:op a)))
  (let [f (:fn a)
        fn-op (-> a :fn :op)]
    (condp = fn-op
      :var (some-> a :fn :var data/get-var-analysis get-var-fn-analysis)
      :the-var (some-> a :fn :var data/get-var-analysis get-var-fn-analysis)
      :fn  (-> a :fn)
      :local (-> a (find-binding (-> a :fn :name)) :init)
      :const nil
      :invoke (recur (:fn a))
      (println "don't know how to find analysis for" fn-op))))

(defmethod flow :invoke [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        fn-spec (-> a :fn ::ret-spec)
        args-spec (analysis-args->spec (:args a))
        arg-count (count (:args a))
        f-a (invoke-get-fn-analysis a)]
    (assert (c/spect? fn-spec))
    (assert (c/spect? args-spec))
    (if (or (and f-a (= :fn (:op f-a)) (invoke-valid-arity? f-a arg-count))
            (not f-a)
            (not= :fn (:op f-a)))
      (if fn-spec
        (let [a (assoc a ::fn-spec fn-spec)]
          (assert (c/spect? fn-spec))
          (assert (c/spect? args-spec))
          (assoc a ::ret-spec (c/invoke fn-spec args-spec)))
        (assoc a ::ret-spec (c/unknown {:message (format "no spec for %s" (:var (:fn a)))})))
      (assoc a ::ret-spec (c/invalid {:message (format "wrong number of args %s" (:form a))})))))

(defmethod flow :protocol-invoke [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [v (-> a :fn :var)
        spec (when v
               (c/get-var-fn-spec v))
        a (flow-walk a)
        args-spec (analysis-args->spec (:args a))]
    (if spec
      (assoc a ::ret-spec (c/invoke spec args-spec) ::fn-spec spec)
      (do
        (print-once "warning: no spec for" (:var (:fn a)))
        (assoc a ::ret-spec (c/unknown {:message (format "no spec for %s" (:var (:fn a)))}))))))

(s/fdef variadic? :args (s/cat :s c/spect?) :ret boolean?)
(defn variadic?
  "Truthy if this spec will accept unbounded number of args"
  [s]
  (if (and (c/first-rest? s) (c/regex? s))
    (or (= (dissoc s :ret)
           (dissoc (c/rest* s) :ret))
        (some variadic? (:ps s)))
    false))

(s/fdef cat-count :args (s/cat :s c/cat-spec?) :ret (s/nilable int?))
(defn cat-count
  "If the spect is a non-variadic cat, the number of args it needs. Returns nil when variadic"
  [s]
  (when-not (variadic? s)
    (loop [ret 0
           s s]
      (if s
        (recur (inc ret) (c/rest* s))
        ret))))

(defmethod flow :if [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        test-ret-spec (-> a :test ::ret-spec)
        then-ret-spec (-> a :then ::ret-spec)
        else-ret-spec (-> a :else ::ret-spec)
        _ (when (:test a)
            (assert then-ret-spec (format "missing then-ret-spec: %s %s %s" (-> a :then :op) (-> a :then :form)
                                          (a-loc-str a))))
        _ (when (:else a)
            (assert else-ret-spec (format "missing else-ret-spec: %s %s %s" (-> a :else :op) (-> a :else :form)
                                          (a-loc-str a))))
        _ (assert test-ret-spec)
        truthyness (c/truthyness test-ret-spec)]
    (-> a
        (assoc ::ret-spec (condp = truthyness
                            :truthy then-ret-spec
                            :falsey else-ret-spec
                            :ambiguous (c/or- (->>
                                               [then-ret-spec
                                                else-ret-spec])))))))

(defmethod flow :const [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/value (:val a)))))

(defmethod flow :do [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :ret ::ret-spec))))

(defmethod flow :catch [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (if (:body a)
                          (-> a :body ::ret-spec)
                          (c/value nil)))))
(defmethod flow :try [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/or- (map (fn [e]
                                      (::ret-spec e)) (concat (:body a) (:catches a)))))))

(defmethod flow :instance? [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        s (c/class-spec (:class a))
        arg-spec (-> a :target ::ret-spec)]
    (if (not= (c/unknown? arg-spec))
      (if (c/valid? s arg-spec)
        (assoc a ::ret-spec (c/value true))
        (assoc a ::ret-spec c/reject))
      (assoc a ::ret-spec (c/pred-spec #'boolean?)))))

(s/fdef incompatible-java-method? :args (s/cat :v ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn incompatible-java-method?
  "True if it is not legal to call. Returns truthy for unknown args"
  [arg-spec method-types]
  (not (every? (fn [[s a]]
                 (or (c/unknown? a)
                     (c/valid? s a))) (map vector (mapv java-type->spec method-types) (mapv c/parse-spec (-> arg-spec :ps))))))

(s/fdef compatible-java-method? :args (s/cat :v ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn compatible-java-method?
  "True if args conforming to spec arg-spec can be passed to a method that takes method-types. Returns falsey for unknown args"
  [arg-spec method-types]
  (let [spec (c/cat- (mapv java-type->spec method-types))
        argv (c/cat- (mapv c/parse-spec (-> arg-spec :ps)))]
    (assert argv)
    (c/valid? spec argv)))

(s/def ::reflect-name symbol?)
(s/def ::reflect-return-type ::j/java-type)
(s/def ::reflect-parameter-types ::j/java-args)

(s/def ::reflect-method (s/keys :req-un [::reflect-name ::reflect-return-type ::reflect-parameter-types]))

(s/fdef more-specific? :args (s/cat :v ::reflect-method :m ::reflect-method) :ret integer?)
(defn more-specific-compare
  "sort comparator for two vectors of java args"
  [a b]
  (loop [[a & as] (:parameter-types a)
         [b & bs] (:parameter-types b)]
    (if (and a b)
      (cond
        (or (j/primitive? a) (contains? (parents a) (class b))) 1
        (or (j/primitive? b) (contains? (parents b) (class a))) -1
        :else (recur as bs))
      0)))

(s/fdef most-specific :args (s/cat :vecs (s/coll-of j/reflect-method?)) :ret ::j/java-args)
(defn most-specific
  "Given a seq of vectors of java args, return the most specific method"
  [arg-vecs]
  (-> (sort more-specific-compare arg-vecs) last))

(s/fdef get-java-method :args (s/cat :cls class? :method symbol?) :ret (s/coll-of j/reflect-method?))
(defn get-java-method
  [cls method]
  (some->> (reflect/reflect cls)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Method m)
                           (= method (:name m)))))))

(s/fdef get-conforming-java-method :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret (s/nilable j/reflect-method?))
(defn get-conforming-java-method
  "Returns the java method that conforms to arg-spec "
  [cls method arg-spec]
  (let [ms (get-java-method cls method)]
    (some->> (get-java-method cls method)
             (remove (fn [m]
                       (incompatible-java-method? arg-spec (:parameter-types m))))
             (most-specific))))

(s/fdef get-method! :args (s/cat :cls class? :method symbol? :spec ::c/spect) :ret j/reflect-method?)
(defn get-method!
  ""
  [cls method spec]
  (let [m (get-conforming-java-method cls method spec)]
    (if m
      m
      (throw (Exception. (format "Couldn't find method: %s %s %s" cls method spec))))))

(s/fdef get-java-method-spec :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect :a ::analysis) :ret c/spect?)
(defn get-java-method-spec
  "Return a fake spec for a java interop call"
  [cls method arg-spec a]
  (if-let [m (get-conforming-java-method cls method arg-spec)]
    (let [java-args (->> (mapv java-type->spec (:parameter-types m)))
          ret (c/parse-spec (java-type->spec (:return-type m)))]
      (c/fn-spec (c/map->RegexCat {:ps (mapv c/parse-spec java-args)
                                   :forms java-args
                                   :ret []})
                 (c/parse-spec ret)
                 nil))
    (c/invalid {:message (format "no conforming method for java call: %s %s w/ args %s" cls method (print-str arg-spec))})))

(defn multimethod? [x]
  (instance? clojure.lang.MultiFn x))

(defn defmethod? [a]
  (let [{:keys [class method instance]} a
        v (:var instance)]
    (and (= :instance-call (:op a)) (= method 'addMethod) (some-> v deref multimethod?))))

(s/fdef maybe-flow-multi-method :args (s/cat :a ::analysis) :ret ::analysis)
(defn maybe-flow-multi-method [a]
  (let [{:keys [class method instance]} a
        v (:var instance)]
    (if (defmethod? a)
      (let [[dispatch-val f] (:args a)
            a (assoc-in a [:args 1 ::var] v)]
        (data/store-defmethod-analysis a)
        a)
      a)))

(defn flow-java-call
  "Handles both :static-call and :instance-call"
  [a]
  {:post [(do (when-not (::ret-spec %) (println "flow-java-call:" (:form a) "=>" %)) true) (c/spect? (::ret-spec %))]}
  (let [{:keys [class method instance]} a
        a (flow-walk a)
        a (maybe-flow-multi-method a)
        args-spec (analysis-args->spec (util/zip a :args))
        meth (get-conforming-java-method class method args-spec)
        spec (get-java-method-spec class method args-spec a)
        spec (if (and meth spec (c/known? (:args spec)))
               (c/maybe-transform-method meth spec (analysis-args->spec (:args a)))
               spec)]
    (if (c/fn-spec? spec)
      (assoc a ::ret-spec (or (:ret spec) (c/unknown {:message (format "no :ret spec for %s" spec)}))
             ::args-spec (:args spec))
      (do
        (assert (c/invalid? spec))
        (assoc a ::ret-spec spec)))))

(defmethod flow :static-call [a]
  {:post [(c/spect? (::ret-spec %))]}
  (flow-java-call a))

(defmethod flow :instance-call [a]
  {:post [(c/spect? (::ret-spec %))]}
  (flow-java-call a))

(declare assoc-form-spec)

(s/fdef get-invoke-fn-spec :args (s/cat :a ::analysis) :ret (s/nilable ::c/spect))

(defn get-invoke-fn-spec
  "Given an :fn a, return the spec"
  [a]
  (when (-> a :op (= :var))
    (assert (var? (:var a))))

  (condp = (:op a)
    :var (c/get-var-fn-spec (:var a))))

(defn assoc-invoke-var [a]
  (let [v (-> a :fn :var)
        _ (assert v)
        s (c/get-var-fn-spec v)]
    (if s
      (assoc a
             ::args-spec (:args s)
             ::ret-spec (:ret s))
      a)))

(defmethod flow :local [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [b (find-binding a (:name a))]
    (assert b (format "flow :local: failed to find binding: %s %s" (:name a) (a-loc-str a)))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (c/spect? (::ret-spec b)))
    (assoc a ::ret-spec (::ret-spec b))))

(defn deftype?
  "True if this analysis is inside a deftype"
  [a]
  (if (= :deftype (:op a))
    true
    (if-let [a* (unwrap-a a)]
      (recur a*)
      false)))

(defmethod flow :binding [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (when (:init a)
      (assert (-> a :init ::ret-spec)))
    (assoc a ::ret-spec (cond
                          (:init a) (-> a :init ::ret-spec)
                          (-> a :local (= :this)) (c/class-spec (:tag a))
                          (and (= '__extmap (:name a)) (deftype? a)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                          (and (= '__meta (:name a)) (deftype? a)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                          :else (c/unknown {:message "unknown binding" :form (:form a) :a-loc (a-loc a)})))))

(s/fdef assoc-spec-bindings :args (s/cat :a ::analysis) :ret ::analysis)
(defn assoc-spec-bindings
  "Given the :bindings from a let, assoc ::flow/spec to the binding, based on the right-hand value"
  [a]
  {:post [(every? (fn [b]
                    (c/spect? (::ret-spec b))) (:bindings %))]}
  (reduce (fn [a b]
            (update-in a [:bindings] conj (flow (with-meta b {:a a})))) (assoc a :bindings []) (:bindings a)))

(defn flow-loop-let [a]
  {:post [(spect-or-control-flow? (::ret-spec %))]}
  (let [a (assoc-spec-bindings a)
        a (flow-walk a)
        ret-spec (::ret-spec (:body a))]
    (assert ret-spec)
    (assoc a ::ret-spec ret-spec)))

(defmethod flow :let [a]
  {:post [(spect-or-control-flow? (::ret-spec %))]}
  (flow-loop-let a))

(defmethod flow :loop [a]
  {:post [(spect-or-control-flow? (::ret-spec %))]}
  (flow-loop-let a))

(s/fdef method-arity-conform :args (s/cat :params (s/coll-of ::ana.jvm/binding) :args c/spect?))
(defn method-arity-conform?
  "Given the :fn-method params and invoke spec args, return true if this call conforms"
  [params args]
  (loop [params params
         args args]
    (if (and params args)
      (if (:variadic? (first params))
        true
        (if (empty? params)
          (if (c/accept-nil? args)
            true
            false)
          (if (and (first params) (c/first* args))
            (let [params* (rest params)
                  args* (c/rest* args)]
              (if (and params* args*)
                (recur params* args*)
                (if (and (nil? (seq params*)) (nil? args*))
                  true
                  false)))
            false)))
      false)))

(s/fdef arity-conform? :args (s/cat :spec ::c/spect :params ::ana.jvm/bindings) :ret boolean?)
(defn arity-conform?
  "Without knowing the types of args, return true if it's possible for args to conform, based on arity alone"
  [spec args]
  (if (and spec args (c/first-rest? spec))
    (if (:variadic? (first args))
      true
      (if (empty? args)
        (if (c/accept-nil? spec)
          true
          false)
        (let [spec* (c/rest* spec)
              args* (seq (rest args))]
          (if (and spec* args*)
            (recur spec* args*)
            (if (and (nil? spec*) (nil? args*))
              true
              false)))))
    false))

(s/fdef destructure-fn-params :args (s/cat :params ::ana.jvm/bindings :spec ::c/spect :a ::analysis) :ret ::ana.jvm/bindings)
(defn destructure-fn-params
  "Given a spect and ana.jvm/fn-method params, update params to include spec"
  [params spec a]
  (if (arity-conform? spec params)
    (loop [ret []
           params params
           spec spec]
      (if (and (seq params)
               spec)
        (let [param (first params)
              s (c/first* spec)]
          (if (:variadic? param)
            (conj ret (assoc param ::ret-spec (c/rest* spec)))
            (recur (conj ret (assoc param ::ret-spec s)) (rest params) (c/rest* spec))))
        ret))
    (mapv (fn [p]
            (assoc p ::ret-spec (c/unknown {:form (:name p) :message "destructure failed"}))) params)))

(s/fdef strip-control-flow :args (s/cat :s (s/nilable c/spect?)) :ret (s/nilable c/spect?))
(defn strip-control-flow
  "Given the ret-spec for a function, remove control flow (recur and throw) from the type."
  [s]
  {:post [(s/nilable (c/spect? %))]}
  (let [s (if (satisfies? c/Compound s)
            (c/remove* (fn [p] (control-flow? p)) s)
            s)
        s (if (satisfies? c/Compound s)
            (c/map* strip-control-flow s)
            s)]
    s))

(defn flow-method* [a args]
  (let [a (flow-walk a)
        a (if args
            (update-in a [:params] destructure-fn-params args a)
            (update-in a [:params] (fn [params]
                                     (mapv (fn [p]
                                             (assoc p ::ret-spec (c/unknown {:message (format "no spec for %s" (:form (unwrap-a a))) :form (:name p) :a-loc (a-loc a)}))) params))))
        a (update-in a [:body] (fn [body]
                                 (flow (with-meta body {:a a}))))
        body-ret-spec (strip-control-flow (::ret-spec (:body a)))]
    (assoc a ::ret-spec body-ret-spec)))

(defn flow-method [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [v (-> a meta :a ::var)
        s (when v
            (c/get-var-fn-spec v))
        a (flow-method* a (:args s))
        ret-spec (::ret-spec a)]
    a))

(defmethod flow :fn-method [a]
  {:post [(c/spect? (::ret-spec %))]}
  (flow-method a))

(defmethod flow :method [a]
  {:post [(c/spect? (::ret-spec %))]}
  (flow-method a))

(defmethod flow :vector [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/value (mapv ::ret-spec (:items a))))))

(defmethod flow :map [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        ret-keys (reduce (fn [ret-keys [k-a v-a]]
                           (let [k-s (::ret-spec k-a)]
                             (if (and (c/value? k-s) (keyword? (:v k-s)))
                               (let [key-type (if (qualified-keyword? (:v k-s))
                                                :req
                                                :req-un)]
                                 (assoc-in ret-keys [key-type (:v k-s)] (::ret-spec v-a)))
                               ret-keys))) {:req {}
                                            :req-un {}} (map vector (:keys a) (:vals a)))
        ret-spec (c/keys-spec (:req ret-keys) (:req-un ret-keys) {} {})]
    (assoc a ::ret-spec ret-spec)))

(defmethod flow :recur [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (recur-form (analysis-args->spec (:exprs a))))))

(defmethod flow :throw [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/unknown {:form {:exception (-> a :exception :class :val)}
                                    :message "form thows exception"}))))

(s/fdef keyword-invoke-ret-spec :args (s/cat :a ::analysis) :ret c/spect?)
(defn keyword-invoke-ret-spec
  [a]
  {:post [(c/spect? %)]}
  (let [a (update-in a [:target] (fn [t]
                                   (flow (with-a t a))))
        spec (-> a :target ::ret-spec)
        k (-> a :keyword :val)]
    (assert k)
    (assert spec)
    (if (c/keyword-invoke? spec)
      (c/keyword-invoke spec (c/cat- [k]))
      (c/value nil))))

(defmethod flow :keyword-invoke [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (keyword-invoke-ret-spec a))))

(defmethod flow :new [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/class-spec (-> a :class :val)))))

(defmethod flow :set! [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (::ret-spec (:val a)))))

(defmethod flow :set [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/coll-of (c/or- (map ::ret-spec (:items a))) #{}))))

(defmethod flow :case [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/or- (map ::ret-spec (:thens a))))))

(defmethod flow :case-test [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :test ::ret-spec))))

(defmethod flow :case-then [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :then ::ret-spec))))

(defmethod flow :monitor-enter [a]
  {:post [(c/spect? (::ret-spec %))]}
  (assoc (flow-walk a) ::ret-spec (c/value nil)))

(defmethod flow :monitor-exit [a]
  {:post [(c/spect? (::ret-spec %))]}
  (assoc (flow-walk a) ::ret-spec (c/value nil)))

(defmethod flow :import [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/class-spec Class))))

(defn get-java-field
  [class field & [{:keys [static?]}]]
  (some->> (reflect/reflect class)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Field m)
                           (if static?
                             (contains? (:flags m) :static))
                           (= field (:name m)))))
           first))

(defmethod flow :static-field [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        {:keys [field class]} a]
    (assoc a ::ret-spec (c/class-spec (:type (get-java-field class field {:static? true}))))))

(defmethod flow :instance-field [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)
        {:keys [field class]} a]
    (assoc a ::ret-spec (c/class-spec (:type (get-java-field class field))))))

(defmethod flow :reify [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/and-spec (mapv c/class-spec (:interfaces a))))))

(defmethod flow :deftype [a]
  {:post [(c/spect? (::ret-spec %))]}
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/class-spec (:class-name a)))))


(s/fdef get-fn-method-invoke :args (s/cat :a ::ana.jvm/fn :args c/spect?))
(defn get-fn-method-invoke
  "given an :fn analysis and spect args, return the :fn-method that would be invoked"
  [a args]
  (assert (= :fn (:op a)))
  (let [methods (:methods a)]
    (->> methods
         (filter (fn [m]
                   (method-arity-conform? (:params m) args)))
         first)))

(s/fdef invoke-with-var :args (s/cat :v var? :args any?) :ret c/spect?)
(defn invoke-with-var
  "v must already be analyzed"
  [v args]
  (if-let [s (c/get-var-fn-spec v)]
    (if (c/conform-var-args? v args)
      (if-let [a (data/get-var-analysis v)]
        (let [a (-> a :init :expr)]
          (if-let [method (get-fn-method-invoke a args)]
            (-> (flow-method* method args) ::ret-spec)
            (c/invalid {:form `(v ~args) :message (format "invoke args don't conform: %s %s" v args)})))
        (c/unknown {:form `(~v ~args) :message (format "var %s not analyzed" v)}))
      (c/invalid {:form `(~v ~args) :message (format "invoke-with-var does not conform: %s %s" v args)}))
    (c/unknown {:form `(v ~args) :message (format "invoke-with-var:" v "no spec")})))

(s/fdef invoke-a-dispatch :args (s/cat :a ::analysis) :ret keyword?)
(defn invoke-a-dispatch [x]
  (:op x))

(s/fdef invoke-a :args (s/cat :x ::analysis) :ret c/spect?)
(defmulti invoke-a "Given an analysis form that's an invoke, predict the return type" #'invoke-a-dispatch)

(defmethod invoke-a :default [a]
  (c/unknown {:form (:form a) :a-loc a :message (format "don't know how to invoke %s" (:op a))}))

(s/fdef a-multimethod? :args (s/cat :a ::ana.jvm/analysis) :ret boolean?)
(defn a-multimethod? [a]
  (and (-> a :init :op (= :new))
       (-> a :init :class :val (= clojure.lang.MultiFn))))

(s/fdef var-fn? :args (s/cat :v var?) :ret boolean?)
(defn var-fn?
  "True if this var holds a fn"
  [v]
  (if-let [a (data/get-var-analysis v)]
    (boolean
     (or (some-> a :init maybe-strip-meta :op (= :fn))
         (a-multimethod? a)))
    (do
      (println (format "Couldn't find var %s in analysis cache:" v))
      false)))

(s/fdef wrong-number-args-error :args (s/cat :f ::analysis :a ::analysis) :ret c/spect?)
(defn wrong-number-args-error [f a]
  (let [arities (-> f :methods (->> (map :arglist) (str/join " or ")))]
    (c/invalid {:message (format "Function %s called with incorrect number of args. Expected %s, got %s" (-> a :form first) arities (->> a :form rest vec))})))

(s/fdef check-invoke-fn-arity :args (s/cat :f ::analysis :args ::analysis) :ret (s/nilable c/spect?))
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

(s/fdef check-invoke-fn-spec :args (s/cat :v var? :s c/fn-spec? :a ::analysis) :ret c/spect?)
(defn check-invoke-fn-spec
  [v s a]
  (let [a-args (zip a :args)
        args-spec (analysis-args->spec a-args)]
    (assert (:args s))
    (if (c/valid? (:args s) a-args)
      (if (:ret s)
        (:ret s)
        (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "no ret spec on %s" s)}))
      (c/invalid {:form (:form a)
                  :a-loc (a-loc a)
                  :message (format "invoke of %s does not conform. expected %s, got %s. " v (print-str (-> s :args)) (print-str args-spec))} a))))

(defmethod invoke-a :var [a]
  (let [v (-> a :fn :var)
        va (-> v data/get-var-analysis maybe-strip-meta)]
    (or
     (when-not va
       (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "no analysis for %s" v)}))
     (when (and va (not (var-fn? v)))
       (c/invalid {:form (:form a)
                   :error {:message (format "attempt to call non-fn var: %s" (:form a))}}))
     (when va
       (check-invoke-fn-arity va a))
     (if-let [s (c/get-var-fn-spec v)]
       (check-invoke-fn-spec v s a)
       (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "invoke: no spec for %s" v)})))))

(defn maybe-check-defmethod [a]
  (if (defmethod? a)
    (let [[dispatch-val f] (:args a)]
      ;; TODO flow-default, check-default, :children. defmethod checking is broken because we don't recurse automatically.
      ;;
      )
    (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "don't know how to check defmethod %s" (:form a))})))

(defn java-methods-str [cls method]
  (->> (get-java-method cls method)
       (mapv :parameter-types)
       (str/join ", ")))

(defn a->java-static-method-name [a]
  (str (:class a) "/" (:method a)))

(defmethod invoke-a :static-call [a]
  (let [a-args (zip a :args)
        args-spec (analysis-args->spec a-args)
        call-spec (::args-spec a)]
    (if call-spec
      (if (c/known? call-spec)
        (if args-spec
          (if-let [valid? (c/valid? call-spec args-spec)]
            (if-let [ret (::ret-spec a)]
              ret
              (c/unknown {:form (:form a) :message (format "no ret-spec on %s" (:form a) :a-loc (a-loc a))}))
            (c/invalid {:form (:form a)
                        :a-loc (a-loc a)
                        :message (format "Java Method %s cannot be called with args %s. Expected %s" (a->java-static-method-name a) (print-str args-spec) (print-str call-spec))} a))
          (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "Calling Java method %s unknown spec, given %s, possible: %s" (a->java-static-method-name a) (print-str args-spec) (java-methods-str (:class a) (:method a)))} a)))
      (c/invalid {:form (:form a) :a-loc (a-loc a) :message (format "Calling Java method: no compatible args for %s. Given %s Possible: %s" (a->java-static-method-name a) (print-str args-spec) (java-methods-str (:class a) (:method a)))} a))))
