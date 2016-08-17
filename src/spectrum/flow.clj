(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.java :as j]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)])
  (:import clojure.lang.Var))

(declare recur?)
(declare find-binding)

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(s/def ::args-spec ::c/spect)
(s/def ::ret-spec any?)
(s/def ::var (s/with-gen (s/spec var?)
               (fn []
                 (gen/elements [#'int? #'println #'str]))))

(s/def ::analysis (s/merge ::ana.jvm/analysis (s/keys :opt [::var ::args-spec ::ret-spec])))

(s/def ::analysis? (s/nilable ::analysis))

(s/def ::analyses (s/coll-of ::analysis))

(defn a-loc [a]
  (select-keys a [:file :line :column]))

(defn a-loc-str
  "A human-formatted string for the file & line of the current analysis"
  [a]
  (let [{{:keys [file line column]} :env} a]
    (str "file " file " line " line " col " column)))

(defrecord RecurForm [args])

(defrecord ThrowForm [exception])

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

(s/fdef throw-form :args (s/cat :e throwable?) :ret throw?)
(defn throw-form [e]
  (map->ThrowForm {:exception e}))

(s/fdef control-flow? :args (s/cat :x any?) :ret boolean?)
(defn control-flow? [x]
  (or (throw? x) (recur? x)))

(s/def ::control-flow control-flow?)

(s/fdef flow-dispatch :args (s/cat :a ::analysis) :ret keyword?)
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

(defn var-named-predicate?
  "True if the var's name looks like a predicate"
  [v]
  (boolean (re-find #"\?$" (name (.sym ^Var v)))))

(s/fdef var-predicate? :args (s/cat :v var?) :ret boolean?)
(defn var-predicate?
  [v]
  (let [s (c/get-var-fn-spec v)]
    (if s
      (and (-> s :args c/cat-spec?)
           (-> s :args :ps count (= 1))
           (-> s :ret (= (c/parse-spec #'boolean?)))
           (var-named-predicate? v))
      false)))

(defn invoke-predicate?
  "True if the analysis is invoking a predicate"
  [a]
  (and (-> a :op (= :invoke))
       (-> a :fn :op (= :var))
       (-> a :args count (= 1))
       (some-> a :fn :var var-predicate?)))

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
    (walk-a flow a)
    (catch Throwable t
      (println "while walking:" (a-loc-str a) (:form a))
      (throw t))))

(defmethod flow :default [a]
  (println "flow :default" (:form a) (:op a))
  (flow-walk a))

(defmethod flow :quote [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :expr ::ret-spec))))

(defmethod flow :def [a]
  (data/store-var-analysis a)
  (let [a (maybe-assoc-var-name a)
        a (flow-walk a)]
    (assoc a ::ret-spec (c/parse-spec #'var?))))

(defmethod flow :the-var [a]
  ;; the-var => (var foo). Returns the actual var
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/parse-spec #'var?))))

(defmethod flow :var [a]
  ;; :var => the value the var holds
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (if-let [s (c/get-var-fn-spec (:var a))]
                          s
                          @(:var a)))))

(defmethod flow :with-meta [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (::ret-spec (:expr a)))))

(defmethod flow :fn [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/parse-spec (s/and fn? ifn?)))))

(defn find-binding*-dispatch [a name]
  (:op a))

(defmulti find-binding* #'find-binding*-dispatch)

(defmethod find-binding* :default [a name]
  nil)

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
  {:post [(do (when %
                (print-once "warning: no spec for deftype field" name)) true)]}
  (->> a
       :fields
       (filter (fn [b] (= name (:name b))))
       first))

(defmethod find-binding* :catch [a name]
  (when (-> a :local :name (= name))
    (:local a)))

(defn binding-update-if-specs
  "Given a :binding, walk up the tree to find all :if predicate tests it contains, and update the spec"
  [a binding]
  (loop [a a
         spec (::ret-spec binding)]
    (when-not spec
      (println "binding-update-if-specs:" (:form a) (:name binding)))
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
                this (get parent this-expr)]

            (if (and (invoke-predicate? test)
                     (-> test :args first :name (= (:name binding))))
              (if (= this-expr :then)
                (recur parent (c/and-spec [spec (c/pred-spec (-> test :fn :var))]))
                (recur parent spec))  ;; TODO add (not pred) to spec here.
              (recur parent spec)))
          (recur parent spec)))
      (assoc binding ::ret-spec spec))))

(s/fdef find-binding :args (s/cat :a ::analysis :name symbol?) :ret (s/nilable ::analysis))
(defn find-binding
  "recursively unwrap a, looking for a :binding for 'name"
  [a name]
  (loop [a* a]
    (when a*
      (if-let [b (find-binding* a* name)]
        (binding-update-if-specs a b)
        (when-let [a* (unwrap-a a*)]
          (recur a*))))))

(s/fdef analysis-args->spec :args (s/cat :a ::analyses) :ret ::c/spect)
(defn analysis-args->spec
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/map->RegexCat {:ps (mapv (fn [arg]
                                (assert (contains? arg ::ret-spec))
                                (::ret-spec arg)) args)
                    :ret []}))

(defn invoke-spec [v spec args-spec]
  (let [s* (c/maybe-transform v args-spec)
        transformed? (not= spec s*)
        conf (c/conform spec args-spec)]
    (if transformed?
      s*
      (if (and (var-predicate? v)
               (c/valid? (c/pred-spec v) (c/first* args-spec)))
        (let [c (c/conform (c/pred-spec v) (c/first* args-spec))
              t (c/truthyness c)]
          (if (not= :ambiguous t)
            (assoc spec :ret (if (= t :truthy)
                               true
                               false))))
        spec))))

(defmethod flow :invoke [a]
  (let [v (-> a :fn :var)
        spec (when v
               (c/get-var-fn-spec v))
        a (flow-walk a)
        args-spec (analysis-args->spec (:args a))
        spec (when spec
               (invoke-spec v spec args-spec))]
    (if v
      (if spec
        (let [a (assoc a ::fn-spec spec)]
          (if (:ret spec)
            (assoc a ::ret-spec (:ret spec))
            (do
              (print-once "warning: no ret-spec for" (:var (:fn a)))
              (assoc a ::ret-spec (c/unknown (:form a) (a-loc a))))))
        (do
          (print-once "warning: no spec for" (:var (:fn a)))
          (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))
      (assoc a ::ret-spec (c/unknown (:form a) (a-loc a))))))

(defmethod flow :protocol-invoke [a]
  (let [v (-> a :fn :var)
        spec (when v
               (c/get-var-fn-spec v))
        a (flow-walk a)
        spec (when spec
               (c/maybe-transform v (analysis-args->spec (:args a))))]
    (if v
      (if spec
        (assoc a ::ret-spec (:ret spec)
                 ::fn-spec spec)
        (do
          (print-once "warning: no spec for" (:var (:fn a)))
          (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))
      (do
        (print-once "warning: invoke non-var unknown:" (:form (:fn a)) (a-loc-str a))
        (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))))

(s/fdef maybe-strip-meta :args (s/cat :a ::analysis) :ret ::analysis)
(defn maybe-strip-meta
  "If a is a :op :with-meta, strip it and return the :expr, or a"
  [a]

  (if (-> a :op (= :with-meta))
    (-> a :expr)
    a))

(s/fdef variadic? :args (s/cat :s ::c/spect) :ret boolean?)
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
  (let [a (flow-walk a)
        then-ret-spec (-> a :then ::ret-spec)
        else-ret-spec (-> a :else ::ret-spec)
        test-ret-spec (-> a :test ::ret-spec)
        truthyness (c/truthyness test-ret-spec)]
    (-> a
        (assoc ::ret-spec (condp = truthyness
                            :truthy then-ret-spec
                            :falsey else-ret-spec
                            :ambiguous (c/or- (->>
                                               [then-ret-spec
                                                else-ret-spec])))))))

(defmethod flow :const [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (:val a))))

(defmethod flow :do [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :ret ::ret-spec))))

(defmethod flow :catch [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (if (:body a)
                          (-> a :body ::ret-spec)
                          nil))))
(defmethod flow :try [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/or- (map (fn [e]
                                      (::ret-spec e)) (concat (:body a) (:catches a)))))))

(defmethod flow :instance? [a]
  (let [a (flow-walk a)
        s (c/class-spec (:class a))
        arg-spec (-> a :target ::ret-spec)]
    (if (not= (c/unknown? arg-spec))
      (if (c/valid? s arg-spec)
        (assoc a ::ret-spec true)
        (assoc a ::ret-spec c/reject))
      (assoc a ::ret-spec (c/parse-spec #'boolean?)))))

(s/fdef compatible-java-method? :args (s/cat :v ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn compatible-java-method?
  "True if args conforming to spec s can be passed to a method that takes method-types"
  [arg-spec method-types]
  (let [spec (c/cat- (mapv java-type->spec method-types))
        argv (-> arg-spec :ps)]
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
             (filterv (fn [m]
                        (compatible-java-method? arg-spec (:parameter-types m))))
             (most-specific))))

(s/fdef get-method! :args (s/cat :cls class? :method symbol? :spec ::c/spect) :ret j/reflect-method?)
(defn get-method!
  ""
  [cls method spec]
  (let [m (get-conforming-java-method cls method spec)]
    (if m
      m
      (throw (Exception. (format "Couldn't find method: %s %s %s" cls method spec))))))

(s/fdef get-java-method-spec :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect :a ::analysis) :ret c/fn-spec?)
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
    (do
      (println "get-java-method-spec: no conforming:" cls method arg-spec "possible:" (mapv :parameter-types (get-java-method cls method)) (a-loc-str a))
      (c/fn-spec (c/unknown nil) (c/unknown nil) nil))))

(defn multimethod? [x]
  (instance? clojure.lang.MultiFn x))

(defn defmethod? [a]
  (let [{:keys [class method instance]} a
        v (:var instance)]
    (and (= :instance-call (:op a)) (= method 'addMethod) (some-> v deref multimethod?))))

(defn maybe-flow-multi-method [a]
  (let [{:keys [class method instance]} a
        v (:var instance)]
    (if (defmethod? a)
      (let [[dispatch-val f] (:args a)]
        (assoc-in a [:args 1 ::var] v)
        a)
      a)))

(defn flow-java-call
  "Handles both :static-call and :instance-call"
  [a]
  (let [{:keys [class method instance]} a
        a (flow-walk a)
        a (maybe-flow-multi-method a)
        args-spec (analysis-args->spec (util/zip a :args))
        meth (get-conforming-java-method class method args-spec)
        spec (get-java-method-spec class method args-spec a)

        spec (if (and meth spec (c/known? (:args spec)))
               (c/maybe-transform-method meth spec (analysis-args->spec (:args a)))
               spec)]
    (when-not (:ret spec)
      (println "flow-java-call: no spec:" class method args-spec))
    (assert (:ret spec))
    (-> a
        (assoc ::ret-spec (:ret spec)
               ::args-spec (:args spec)))))

(defmethod flow :static-call [a]
  (flow-java-call a))

(defmethod flow :instance-call [a]
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

;; (s/fdef get-form-spec :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)
;; (defn get-form-spec
;;   "Given the :init of a binding, return the spec for the form, if any"
;;   [a]
;;   (or (::spec a) (assoc-form-spec a)))

(defmethod flow :local [a]
  (let [b (find-binding a (:name a))]
    (assert b (format "flow :local: failed to find binding: %s %s" (:name a) (a-loc-str a)))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (::ret-spec b))
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
  (let [a (flow-walk a)]
    (when (:init a)
      (assert (-> a :init ::ret-spec)))
    (assoc a ::ret-spec (cond
                          (:init a) (-> a :init ::ret-spec)
                          (-> a :local (= :this)) (c/class-spec (:tag a))
                          (and (= '__extmap (:name a)) (deftype? a)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                          (and (= '__meta (:name a)) (deftype? a)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                          :else (c/unknown (:form a) (a-loc a))))))

(s/fdef assoc-spec-bindings :args (s/cat :a ::analysis) :ret ::analysis)
(defn assoc-spec-bindings
  "Given the :bindings from a let, assoc ::flow/spec to the binding, based on the right-hand value"
  [a]
  {:post [(every? ::ret-spec (:bindings %))]}
  (reduce (fn [a b]
            (update-in a [:bindings] conj (flow (with-meta b {:a a})))) (assoc a :bindings []) (:bindings a)))

(defn flow-loop-let [a]
  (let [a (assoc-spec-bindings a)
        a (flow-walk a)
        ret-spec (::ret-spec (:body a))]
    (assert ret-spec)
    (-> a
        (assoc ::ret-spec ret-spec))))

(defmethod flow :let [a]
  (flow-loop-let a))

(defmethod flow :loop [a]
  (flow-loop-let a))

(s/fdef arity-conform? :args (s/cat :spec ::c/spect :params ::ana.jvm/bindings) :ret boolean?)
(defn arity-conform?
  "Without knowing the types of args, return true if it's possible for args to conform, based on arity alone"
  [spec args]
  (if (and spec args (c/regex? spec))
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
          (assert s)
          (if (:variadic? param)
            (conj ret (assoc param ::ret-spec (c/rest* spec)))
            (recur (conj ret (assoc param ::ret-spec s)) (rest params) (c/rest* spec))))
        ret))
    (do
      (println "destructure failed:" (a-loc-str a) "params are all unknown")
      (mapv (fn [p]
              (assoc p ::ret-spec (c/unknown (:name p) (a-loc a)))) params))))


(defn strip-control-flow
  "Given the ret-spec for a function, remove control flow (recur and throw) from the type."
  [s]
  (if (satisfies? c/Compound s)
    (->> s
         (c/remove* (fn [p]
                      (control-flow? p)))
         (c/map* strip-control-flow))
    s))

(defn flow-method [a]
  (let [v (-> a meta :a ::var)
        s (when v
            (c/get-var-fn-spec v))
        a (flow-walk a)
        a (if s
            (update-in a [:params] destructure-fn-params (:args s) a)
            (update-in a [:params] (fn [params]
                                     (mapv (fn [p]
                                             (assoc p ::ret-spec (c/unknown (:name p) (a-loc a)))) params))))
        a (update-in a [:body] (fn [body]
                                 (flow (with-meta body {:a a}))))]
    (assoc a ::ret-spec (strip-control-flow (::ret-spec (:body a))))))

(defmethod flow :fn-method [a]
  (flow-method a))

(defmethod flow :method [a]
  (flow-method a))

(defmethod flow :vector [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (mapv ::ret-spec (:items a)))))

(defmethod flow :map [a]
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
        ret-spec (c/and-spec [(c/pred-spec #'map?) (apply c/keys-spec (concat (vals ret-keys) [{} {}]))])]
    (assoc a ::ret-spec ret-spec)))

(defmethod flow :recur [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (recur-form (analysis-args->spec (:exprs a))))))

(defmethod flow :throw [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (throw-form (:exception a)))))

(defn keyword-invoke-ret-spec
  [a]
  {:post [(c/spect? %)]}
  (let [a (update-in a [:target] (fn [t]
                            (flow (with-a t a))))
        target-ret-spec (-> a :target ::ret-spec)
        k (-> a :keyword :val)]
    (assert k)
    (assert target-ret-spec)
    (or
     (cond
       (and (c/value? target-ret-spec) (map? (:v target-ret-spec))) (get-in target-ret-spec [:v k])
       (c/keys-spec? target-ret-spec) (or (get-in target-ret-spec [:req-un k])
                                          (get-in target-ret-spec [:opt-un k])))
     (c/unknown (:form a) (a-loc a)))))

(defmethod flow :keyword-invoke [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (keyword-invoke-ret-spec a))))

(defmethod flow :new [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/class-spec (-> a :class :val)))))

(defmethod flow :set! [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (::ret-spec (:val a)))))

(defmethod flow :set [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/coll-of (c/or- (map ::ret-spec (:items a))) #{}))))

(defmethod flow :case [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/or- (map ::ret-spec (:thens a))))))

(defmethod flow :case-test [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :test ::ret-spec))))

(defmethod flow :case-then [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (-> a :then ::ret-spec))))

(defmethod flow :monitor-enter [a]
  (assoc (flow-walk a) ::ret-spec nil))

(defmethod flow :monitor-exit [a]
  (assoc (flow-walk a) ::ret-spec nil))

(defmethod flow :import [a]
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
  (let [a (flow-walk a)
        {:keys [field class]} a]
    (assoc a ::ret-spec (c/class-spec (:type (get-java-field class field {:static? true}))))))

(defmethod flow :instance-field [a]
  (let [a (flow-walk a)
        {:keys [field class]} a]
    (assoc a ::ret-spec (c/class-spec (:type (get-java-field class field))))))

(defmethod flow :reify [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/and-spec (mapv c/class-spec (:interfaces a))))))

(defmethod flow :deftype [a]
  (let [a (flow-walk a)]
    (assoc a ::ret-spec (c/class-spec (:class-name a)))))

(defn analyze+flow [form]
  (flow (ana.jvm/analyze form)))

(defn analyze+flow-ns [ns]
  (mapv flow (ana.jvm/analyze-ns ns)))
