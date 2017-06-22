(ns spectrum.flow
  (:require [clojure.core.memoize :as memo]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]
            [clojure.string :as str]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.java :as j]
            [spectrum.util :as util :refer (print-once protocol? namespace? validate!)])
  (:import [clojure.lang Var Namespace]))

(declare recur?)
(declare find-binding)

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(defrecord RecurForm [args]
  c/Spect
  (conform* [this x]
    false)
  c/Truthyness
  (truthyness [this]
    :ambiguous)
  c/WillAccept
  (will-accept [this]
    #{}))

(defrecord ThrowForm [exception-class]
  c/Spect
  (conform* [this x]
    false)
  c/Truthyness
  (truthyness [this]
    :ambiguous)
  c/WillAccept
  (will-accept [this]
    #{}))

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

(s/fdef flow-dispatch :args (s/cat :a ::ana.jvm/analysis :path vector?) :ret keyword?)
(defn flow-dispatch [a path]
  (-> a (get-in path) :op))

;;; Flowing takes the full form, and a `get-in path to the current
;;; form we're analyzing. flow `get-in the current node, and return
;;; the updated outer node. Reason for this is some operations ,like
;;; inference, need to update their parent values.

;;; Flow fns that take a + path should update the child at path

(defmulti flow*
  "Given an analysis, walk and update-in the the analysis attaching ::args-spec and ::ret-spec to values"
  #'flow-dispatch)

(s/fdef flow :args (s/cat :a ::ana.jvm/analysis) :ret ::analysis)
(defn flow [a]
  (flow* a []))

(s/fdef flow-ns :args (s/cat :as ::analyses) :ret ::analyses)

(defn infer-dispatch [a path]
  (-> a (get-in path) :op))

(defmulti infer* #'infer-dispatch)

(defn infer-
  "Given an :fn analysis, return our best guess for the spec"
  [a]
  {:pre [(do (println "infer push " (:form a)) true)]
   :post [(do (println "infer pop" (:form a) "=>" %) true) (c/spect? %)]}
  (::ret-spec (infer* a [])))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis) :ret c/spect?)
(def infer (memo/memo infer-))

(defn flow-ns
  "Given the result of analyze-ns, flow all forms"
  [as]
  (mapv flow as))

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

(defn assoc-in-a [a path data]
  (if (seq path)
    (assoc-in a path data)
    data))

(defn flow-walk-f [a path]
  (try
    (let [a* (get-in a path)]
      (assert a*)
      (binding [*a* a*]
        (let [a* (get-in a path)
              _ (assert a*)
              a (flow* a path)
              a* (get-in a path)]
          (validate! ::c/spect-like (::ret-spec a*))
          a)))
    (catch Throwable t
      (println "flow-walk exception while walking:" (a-loc-str a) (:form a))
      (throw t))))

(s/fdef walk-a :args (s/cat :f fn? :a ::ana.jvm/analysis :path vector?) :ret ::analysis)
(defn walk-a [f a path]
  (reduce (fn [a c]
            (if (contains? (get-in a path) c)
              (let [new-path (conj path c)
                    c-node (get-in a new-path)]
                (if (sequential? c-node)
                  (reduce (fn [a i]
                            (f a (conj new-path i))) a (range (count c-node)))
                  (f a new-path)))
              a)) a (get-in a (conj path :children))))

(defn flow-walk
  "Walk the children of a*"
  [a path]
  (walk-a flow-walk-f a path))

(defmethod flow* :default [a path]
  (assert false (format "unhandled: %s %s" (:op (get-in a path)) (a-loc-str (get-in a path)))))

(defmethod flow* :quote [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :expr ::ret-spec))))

(defmethod flow* :binding [a path]
  (println "flow* binding:" (get-in a path))
  a)

(defmethod flow* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        a (flow-walk a path)
        a* (get-in a path)]
    (data/store-var-analysis a*)
    (assoc-in a (conj path ::ret-spec) (c/pred-spec #'var?))))

(defmethod flow* :the-var [a path]
  ;; the-var => (var foo). Returns the actual var
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:var a*)))))

(defmethod flow* :var [a path]
  ;; :var => the value the var holds
  (let [a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (if-let [s (c/get-var-fn-spec v)]
                   s
                   (if-let [a (data/get-var-analysis v)]
                     (infer a)
                     (c/value @(:var a*))))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :with-meta [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (::ret-spec (:expr a*)))))

(defmethod flow* :fn [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/parse-spec (s/and fn? ifn?)))))

(defn find-binding*-dispatch [a name]
  (assert (:op a))
  (assert name)
  (:op a))

(defmulti find-binding* #'find-binding*-dispatch)

(defmethod find-binding* :default [a name]
  nil)

(defmethod find-binding* :let [a name]
  (some->> a
           :bindings
           (map-indexed (fn [i b]
                          (assoc b :index i)))
           (filter (fn [b] (= name (:name b))))
           first
           (#(assoc % :path [:bindings (:index %)]))))

(defmethod find-binding* :local [a name]
  (when (and (= (:name a) name) (::ret-spec a))
    a))

(defmethod find-binding* :loop [a name]
  (some->> a
           :bindings
           (map-indexed (fn [i b]
                          (assoc b :index i)))
           (filter (fn [b] (= name (:name b))))
           first
           (#(assoc % :path [:bindings (:index %)]))))

(defmethod find-binding* :binding [a name]
  (when (= name (:name a))
    a))

(defn find-binding-method [a name]
  (some->> a
           :params
           (map-indexed (fn [i b]
                          (assoc b :index i)))
           (filter (fn [b] (= name (:name b))))
           first
           (#(assoc % :path [:params (:index %)]))))

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
  (some->> a
           :fields
           (map-indexed (fn [i b]
                          (assoc b :index i)))
           (filter (fn [b] (= name (:name b))))
           first
           (#(assoc % :path [:fields (:index %)]))))

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

(defn and-not
  "Adds (and s (not x)), removing x from an or-pred if present"
  [s x]
  (cond
    (c/value? s) s ;; adding not to a value doesn't make it more specific
    (c/and-spec? s) (c/and-conj s (c/not-spec x))
    :else (c/and-spec [(maybe-disj-pred s x) (c/not-spec x)])))

(defn binding-update-if-specs
  "Given a :binding, walk up the tree to find all :if predicate tests it contains, and update the spec"
  [a path binding]
  (loop [path path
         spec (::ret-spec binding)]
    (let [a* (get-in a path)]
      (assert spec (format "no ::ret-spec on" binding))
      (if (and a* (seq path))
        (let [parent (get-in a (pop path))]
          (if (= :if (:op parent))
            (let [{:keys [test then else]} parent
                  this-expr (cond
                              (and (= (:form a*) (:form test)) (= (a-loc a*) (a-loc test))) :test
                              (and (= (:form a*) (:form then)) (= (a-loc a*) (a-loc then))) :then
                              (and (= (:form a*) (:form else)) (= (a-loc a*) (a-loc else))) :else
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
                (let [test-pred (condp = test-type
                                  :nil  (c/pred-spec #'nil?)
                                  :pred (c/pred-spec (-> test :fn :var))
                                  :truthy  (c/pred-spec #'identity)
                                  :instance? (c/class-spec (:class test)))
                      _ (assert test-pred)
                      updated-spec-then (condp = test-type
                                          :pred (c/and-spec [spec test-pred])
                                          :nil (c/value nil)
                                          :truthy (-> spec (and-not (c/pred-spec #'nil?)) (and-not (c/pred-spec #'false?)))
                                          :instance? (c/and-spec [spec (c/class-spec (:class test))]))
                      updated-spec-else  (condp = test-type
                                           :pred (and-not spec test-pred)
                                           :nil (and-not spec test-pred)
                                           :truthy (c/or- [(c/value nil) (c/value false)])
                                           :instance? (and-not spec test-pred))]
                  (cond
                    (= this-expr :then) (recur parent updated-spec-then)
                    (= this-expr :else) (recur parent updated-spec-else)
                    :else (recur (pop path) spec)))
                (recur (pop path) spec)))
            (recur (pop path) spec)))
        (assoc binding ::ret-spec spec)))))

(s/fdef find-binding :args (s/cat :a ::analysis :path vector? :name symbol?) :ret (s/nilable ::analysis))
(defn find-binding
  "recursively unwrap a, looking for a :binding for 'name"
  [a path name]
  {:pre (symbol? name)
   :post [(s/valid? (s/nilable ::analysis) %)]}
  (loop [path* path]
    (assert (vector? path))
    (let [a* (get-in a path*)
          b (when (:op a*)
              (find-binding* a* name))]
      (if b
        (let [b (assoc b :path (into path* (:path b)))]
          (binding-update-if-specs a path b))
        (when (seq path*)
          (let [p* (pop path*)]
            (recur p*)))))))

(s/fdef add-constraint :args (s/cat :a c/spect? :b c/spect?) :ret c/spect?)
(defn add-constraint
  "Given a spec s, update it to also conform to spec `constraint`"
  [s constraint]
  (cond
    (= (c/pred-spec #'any?) s) constraint
    (c/and-spec? s) (c/and-conj s constraint)
    :else (c/and-spec [s constraint])))

(s/fdef infer-add-constraint :args (s/cat :a ::analysis :b-path vector? :method-spec c/spect?))
(defn infer-add-constraint [a b-path method-spec]
  (let [b (get-in a b-path)]
    (assert (::ret-spec b))
    (update-in a (conj b-path ::ret-spec) add-constraint method-spec)))

(s/fdef analysis-args->spec :args (s/cat :a ::ana.jvm/analyses) :ret ::c/spect)
(defn analysis-args->spec
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/map->RegexCat {:ps (mapv (fn [arg]
                                (when-not (::ret-spec arg)
                                  (println "no ret-spec:" (:form arg) (:op arg)))
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

(defn invoke-get-fn-analysis [a path]
  (let [a* (get-in a path)
        _ (assert (= :invoke (:op a*)) (format "invoke-get-fn-analysis passed %s %s" (:op a*) (:form a*)))
        f (:fn a*)
        fn-op (-> a* :fn :op)]
    (condp = fn-op
      :var (some-> a* :fn :var data/get-var-analysis get-var-fn-analysis)
      :the-var (some-> a* :fn :var data/get-var-analysis get-var-fn-analysis)
      :fn  (-> a* :fn)
      :local (-> a (find-binding path (-> a* :fn :name)) :init)
      :const nil
      :invoke (recur a (conj path :fn))
      (println "don't know how to find analysis for" fn-op))))

(s/fdef invoke-get-fn-spec :args (s/cat :a ::analysis) :ret (s/nilable ::c/spect))

(defn invoke-get-fn-spec-dispatch [a]
  (:op a))

(defmulti invoke-get-fn-spec "Given the :fn from an :invoke a, return the spec for the thing being invoked"
  #'invoke-get-fn-spec-dispatch)

(defmethod invoke-get-fn-spec :var [a]
  {:post [(or (nil? %) (c/spect? %))]}
  (let [v (-> a :var)]
    (assert (var? v))
    (if-let [s (c/get-var-fn-spec v)]
      s
      (if-let [a (data/get-var-analysis v)]
        (infer (-> a :init maybe-strip-meta))
        (c/unknown {:message (format "couldn't find spec or analysis for %s" v)})))))

(defmethod invoke-get-fn-spec :default [a]
  (c/unknown {:message (format "don't know how to get spec or analysis for %s %s" (:op a) (:form a))}))

(defmethod flow* :invoke [a path]
  {:post [(c/spect? (::ret-spec (get-in % path)))]}
  (let [a (flow-walk a path)
        a* (get-in a path)
        fn-spec (-> a* :fn ::ret-spec)
        args-spec (analysis-args->spec (:args a*))
        arg-count (count (:args a*))
        f-a (invoke-get-fn-analysis a path)
        fn-spec (if fn-spec
                  fn-spec
                  (if f-a
                    (infer a path)))]
    (assert (c/spect? fn-spec))
    (assert (c/spect? args-spec))
    (if (or (and f-a (= :fn (:op f-a)) (invoke-valid-arity? f-a arg-count))
            (not f-a)
            (not= :fn (:op f-a)))
      (if fn-spec
        (let [a (assoc-in a (conj path ::fn-spec) fn-spec)]
          (assert (c/spect? fn-spec))
          (assert (c/spect? args-spec))
          (assoc-in a (conj path ::ret-spec) (c/invoke fn-spec args-spec)))
        (assoc-in a (conj path ::ret-spec) (c/unknown {:message (format "invoke: no spec for %s" (:var (:fn a*)))})))
      (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "invoke: wrong number of args %s" (:form a*))})))))

(defn zip-fn-params
  "Given an fnspec and the untyped args to an invoke, bind specs. Returns nil on failure"
  [spec args]
  (let [ss (if (:args spec)
             (filter (fn [as]
                       (= (count args) (count as))) (c/all-possible-values (c/cat-sequential (:args spec))))
             [])
        spec* (apply map (fn [& args]
                           (c/or- args)) ss)]
    (map (fn [a s]
           (assoc a ::ret-spec s)) args spec*)))


(defmethod flow* :protocol-invoke [a path]
  (let [a* (get-in a path)
        v (-> a* :fn :var)
        spec (when v
               (c/get-var-fn-spec v))
        a (flow-walk a path)
        a* (get-in a path)
        args-spec (analysis-args->spec (:args a*))]
    (assoc-in a (conj path ::ret-spec) (if spec
                                         (c/invoke spec args-spec)
                                         (c/unknown {:message (format "protocol-invoke: no spec for %s" (:var (:fn a)))})))))


(s/fdef variadic? :args (s/cat :s c/spect?) :ret boolean?)
(defn variadic?
  "Truthy if this spec will accept unbounded number of args"
  [s]
  (if (and (c/first-rest? s) (c/regex? s))
    (or (= (dissoc s :ret)
           (dissoc (c/rest* s) :ret))
        (some variadic? (:ps s)))
    false))

(s/fdef cat-count :args (s/cat :s c/first-rest?) :ret (s/nilable int?))
(defn cat-count
  "If the spect is a non-variadic cat, the number of args it needs. Returns nil when variadic"
  [s]
  (when-not (variadic? s)
    (loop [ret 0
           s s]
      (if s
        (recur (inc ret) (c/rest* s))
        ret))))

(defmethod flow* :if [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        test-ret-spec (-> a* :test ::ret-spec)
        then-ret-spec (-> a* :then ::ret-spec)
        else-ret-spec (-> a* :else ::ret-spec)
        _ (when (:test a*)
            (assert then-ret-spec (format "missing then-ret-spec: %s %s %s" (-> a* :then :op) (-> a* :then :form)
                                          (a-loc-str a*))))
        _ (when (:else a*)
            (assert else-ret-spec (format "missing else-ret-spec: %s %s %s" (-> a* :else :op) (-> a* :else :form)
                                          (a-loc-str a*))))
        _ (assert test-ret-spec)
        truthyness (c/truthyness test-ret-spec)]

    (assoc-in a (conj path ::ret-spec) (condp = truthyness
                                         :truthy then-ret-spec
                                         :falsey else-ret-spec
                                         :ambiguous (c/or- (->>
                                                            [then-ret-spec
                                                             else-ret-spec]))))))

(defmethod flow* :const [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:val a*)))))

(defmethod flow* :do [a path]
  (let [a (flow-walk a path)]
    (assoc-in a (conj path ::ret-spec) (-> a (get-in path) :ret ::ret-spec))))

(defmethod flow* :catch [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assert (or (map? (:body a*)) (nil? (:body a*))))
    (assoc-in a (conj path ::ret-spec) (if (:body a*)
                                         (-> a* :body ::ret-spec)
                                         (c/value nil)))))
(defmethod flow* :try [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        body (:body a*)
        _ (assert (or (map? body) (vector? body)))
        body (if (map? body)
               [body]
               body)
        catches (:catches a*)]
    (assert (sequential? body))
    (assert (sequential? catches))
    (assert (every? ::ret-spec (concat body catches)))
    (assoc-in a (conj path ::ret-spec) (c/or- (map ::ret-spec (concat body catches))))))

(defmethod flow* :instance? [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        s (c/class-spec (:class a*))
        arg-spec (-> a* :target ::ret-spec)
        ret-spec (if (not= (c/unknown? arg-spec))
                   (if (c/valid? s arg-spec)
                     (c/value true)
                     (c/value false))
                   (c/pred-spec #'boolean?))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defn resolve-java-class-spec [x]
  (c/class-spec (j/resolve-java-class x)))

(s/fdef incompatible-java-method-relaxed? :args (s/cat :arg-spec ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn compatible-java-method-relaxed?
  "True if it is not legal to call. Returns truthy for unknown args"
  [arg-spec method-types]
  (loop [arg-spec arg-spec
         method-spec (c/cat- (mapv resolve-java-class-spec method-types))]
    (if (and (c/first* arg-spec)
             (c/first* method-spec))
      (let [m (c/first* method-spec)
            m-c (c/spec->classes m)
            _ (assert (= 1 (count m-c)))
            m-c (first m-c)
            a (c/first* arg-spec)
            a-c (c/spec->classes a)]
        (if (and (nil? a) (nil? m))
          true
          (if (and m a (or (c/valid? m a) (when (and m-c (seq a-c))
                                            (every? (fn [a-c*]
                                                      (j/castable? m-c a-c*)) a-c)) (c/unknown? a)))
            (recur (c/rest* arg-spec) (c/rest* method-spec))
            false)))
      (if (and (nil? (c/first* arg-spec))
               (nil? (c/first* method-spec)))
        true
        false))))

(s/fdef compatible-java-method? :args (s/cat :v ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn compatible-java-method?
  "True if args conforming to spec arg-spec can be passed to a method that takes method-types. Returns falsey for unknown args"
  [arg-spec method-types]
  (let [spec (c/cat- (mapv resolve-java-class-spec method-types))
        argv (c/cat- (mapv c/parse-spec (-> arg-spec :ps)))]
    (assert argv)
    (c/valid? spec argv)))

(s/def ::reflect-name symbol?)
(s/def ::reflect-return-type class?)
(s/def ::reflect-parameter-types ::j/java-args)

(s/def ::reflect-method (s/keys :req-un [::reflect-name ::reflect-return-type ::reflect-parameter-types]))

(s/fdef more-specific? :args (s/cat :v ::reflect-method :m ::reflect-method) :ret integer?)
(defn more-specific-compare
  "sort comparator for two vectors of java args. more specific is positive. Returns positive when b is more specific than a"
  [a b]
  (loop [[a & as] (:parameter-types a)
         [b & bs] (:parameter-types b)]
    (if (and a b)
      (let [a (j/resolve-java-class a)
            b (j/resolve-java-class b)]
        (do
          (cond
            (j/more-specific? a b) -1
            (j/more-specific? b a) 1
            :else (recur as bs))))
      (do
        (assert (and (not a) (not b)))
        0))))

(defn requires-narrowing?
  "Given an arg spec and java method args, return true if any argument requires narrowing"
  [spec arg-vec]
  (let [s (c/first* spec)
        arg (first arg-vec)]
    (if (and s arg)
      (if (c/known? s)
        (let [cs (c/spec->classes s)
              arg (j/resolve-java-class arg)]
          (if (and cs arg (some (fn [c*]
                                 (j/narrowing? c* arg)) cs))
            true
            (recur (c/rest* spec) (rest arg-vec))))
        false)
      false)))

(s/fdef most-specific :args (s/cat :spec c/spect? :vecs (s/coll-of j/reflect-method?)) :ret ::j/java-args)
(defn most-specific
  "Given a spec and a seq of vectors of java args, return the most specific method"
  [spec methods]
  (let [{wider false
         narrower true} (group-by (fn [method]
                                    (requires-narrowing? spec (:parameter-types method))) methods)]
    (->> (concat (sort more-specific-compare wider)
                 (sort more-specific-compare narrower))
         first)))

(s/fdef get-java-method :args (s/cat :cls class? :method symbol?) :ret (s/coll-of j/reflect-method?))
(defn get-java-method
  [cls method]
  (some->> (reflect/reflect cls)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Method m)
                           (= method (:name m)))))))


(s/fdef get-conforming-java-method :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret (s/nilable (s/coll-of j/reflect-method?)))
(defn get-compatible-java-methods
  "Returns all java method arities that conform to arg-spec "
  [cls method arg-spec]
  (let [ms (get-java-method cls method)]
    (some->> (get-java-method cls method)
             (filter (fn [m]
                       (compatible-java-method-relaxed? arg-spec (:parameter-types m)))))))

(s/fdef get-conforming-java-method :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret (s/nilable j/reflect-method?))
(defn get-conforming-java-method
  "Returns the java method that conforms to arg-spec "
  [cls method arg-spec]
  (let [ms (get-java-method cls method)]
    (some->> (get-java-method cls method)
             (filter (fn [m]
                       (compatible-java-method-relaxed? arg-spec (:parameter-types m))))
             (most-specific arg-spec))))

(s/fdef get-method! :args (s/cat :cls class? :method symbol? :spec ::c/spect) :ret j/reflect-method?)
(defn get-method!
  ""
  [cls method spec]
  (let [m (get-conforming-java-method cls method spec)]
    (if m
      m
      (throw (Exception. (format "Couldn't find method: %s %s %s" cls method spec))))))

(defn class-is-deftype? [cls]
  (isa? cls clojure.lang.IType))

(defn class-is-defrecord? [cls]
  (isa? cls clojure.lang.IRecord))

(s/fdef java-spec-with-nil :args (s/cat :x c/class-spec?) :ret c/spect?)
(defn java-spec-with-nil
  "Java functions are all implicitly (or nil), unless primitive."
  [s]
  (let [c (:cls s)]
    (assert (class? c))
    (if (j/primitive? c)
      s
      (c/or- [s (c/value nil)]))))

(s/fdef defrecord-create? :args (s/cat :cls class? :method symbol?) :ret boolean?)
(defn defrecord-create? [cls method]
  (and (or (class-is-deftype? cls) (class-is-defrecord? cls))
       (= method 'create)))

(s/fdef get-java-method-spec :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret c/spect?)
(defn get-java-method-spec
  "Return a fake spec for a java interop call. Args should *not* include 'this"
  [cls method arg-spec]
  (if-let [m (get-conforming-java-method cls method arg-spec)]
    (let [java-args (->> (mapv resolve-java-class-spec (:parameter-types m))
                         (mapv java-spec-with-nil))
          ret (-> m :return-type resolve-java-class-spec)
          ret (if (defrecord-create? cls method)
                ret
                (java-spec-with-nil ret))]
      (c/fn-spec (c/map->RegexCat {:ps java-args
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
  {:post [(::ret-spec %)]}
  (let [{:keys [class method instance]} a
        a (maybe-flow-multi-method a)
        args-spec (analysis-args->spec (util/zip a :args))
        meth (get-conforming-java-method class method args-spec)
        spec (get-java-method-spec class method args-spec)
        spec (if (and meth spec (c/known? (:args spec)))
               (c/maybe-transform-method meth spec args-spec)
               spec)]

    (if (c/fn-spec? spec)
      (do
        (assert (:ret spec))
        (if (c/every-known? args-spec)
          (assoc a ::ret-spec (:ret spec) ::args-spec (:args spec))
          (assoc a ::ret-spec (c/unknown {:form (:form a) :message (format "invoke %s with unknown args %s" (print-str spec) (print-str args-spec))}))))
      (do
        (assert (c/invalid? spec))
        (assoc a ::ret-spec spec)))))

(defmethod flow* :static-call [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in-a a path (flow-java-call a*))))

(defmethod flow* :instance-call [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        a* (flow-java-call a*)]
    (assert (::ret-spec a*))
    (assoc-in-a a path a*)))

(defmethod flow* :local [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        b (find-binding a path (:name a*))]
    (assert b (format "flow :local: failed to find binding: %s %s %s %s" (:name a*) (:form a*) (a-loc-str a*) (get-in a (pop (pop (pop (pop path)))))))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (c/spect? (::ret-spec b)))
    (assoc-in a (conj path ::ret-spec) (::ret-spec b))))

(defn deftype?
  "True if this analysis is inside a deftype"
  [a path]
  (if (= :deftype (:op (get-in a path)))
    true
    (if (seq path)
      (recur a (pop path))
      false)))

(defmethod flow* :binding [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        ret-spec (cond
                   (::ret-spec a*) (::ret-spec a*)
                   (-> a* :init ::ret-spec) (-> a* :init ::ret-spec)
                   (-> a* :local (= :this)) (c/class-spec (:tag a*))
                   (and (= '__extmap (:name a*)) (deftype? a path)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                   (and (= '__meta (:name a*)) (deftype? a path)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))
                   (and (= '__hash (:name a*)) (deftype? a path)) (c/class-spec Integer/TYPE)
                   (and (= '__hasheq (:name a*)) (deftype? a path)) (c/class-spec Integer/TYPE)
                   :else (c/unknown {:message (format "flow :binding: unknown binding %s %s" (:name a*) path) :form (:form a*) :a-loc (a-loc a*) :path path}))]
    (assert ret-spec)
    (assert (c/spect? ret-spec))
    (swap! (:atom a*) assoc ::ret-spec ret-spec)
    (when (:init a*)
      (assert (-> a* :init ::ret-spec)))
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defn flow-loop-let [a path]
  {:post [(spect-or-control-flow? (::ret-spec (get-in % path)))]}
  (let [a* (get-in a path)
        a (flow-walk a path)
        a* (get-in a path)
        ret-spec (::ret-spec (:body a*))]
    (assert ret-spec)
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :let [a path]
  (flow-loop-let a path))

(defmethod flow* :loop [a path]
  (flow-loop-let a path))

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

(s/fdef destructure-fn-params :args (s/cat :params ::ana.jvm/bindings :spec ::c/spect) :ret ::ana.jvm/bindings)
(defn destructure-fn-params
  "Given a spect and ana.jvm/fn-method params, update params to include spec"
  [params spec]
  {:post [(every? (fn [p] (c/spect? (::ret-spec p))) %)]}
  (if (arity-conform? spec params)
    (loop [ret []
           params params
           spec spec]
      (if (and (seq params)
               spec)
        (let [param (first params)
              s (c/first* spec)]
          (assert (c/spect? s))
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
  (if (satisfies? c/Compound s)
    (let [ps (c/filter* (fn [p] (not (control-flow? p))) s)
          ps (map strip-control-flow ps)]
      (c/new- s ps))
    s))

(s/fdef flow-method* :args (s/cat :a ::analysis :path vector? :args (s/nilable c/spect?)))
(defn flow-method* [a path args]
  (let [a* (get-in a path)
        a (if args
            (update-in a (conj path :params) destructure-fn-params args)
            (update-in a (conj path :params) (fn [params]
                                               (mapv (fn [p]
                                                       (assoc p ::ret-spec (c/unknown {:message (format "method params: no spec for %s" (:form (get-in a (pop path)))) :form (:name p) :a-loc (a-loc a*)}))) params))))
        a (flow* a (conj path :body))
        body (get-in a (conj (conj path :body)))
        body-ret-spec (strip-control-flow (::ret-spec body))]
    (validate! ::c/spect-like body-ret-spec)
    (assoc-in a (conj path ::ret-spec) body-ret-spec)))

(defn flow-method [a path]
  (let [a* (get-in a path)
        v (-> a (get-in (pop (pop path))) ::var)
        s (when v
            (c/get-var-fn-spec v))
        a (flow-method* a path (:args s))
        ret-spec (::ret-spec a)]
    a))

(defmethod flow* :fn-method [a path]
  ;; fn arity
  (flow-method a path))

(defn munged-namespaces []
  (into {} (map (fn [ns]
                  [(munge ns) ns]) (all-ns))))

(s/fdef protocol-ns :args (s/cat :protocol-class class?) :ret (s/nilable namespace?))
(defn protocol-ns
  "Return the ns where a protocol is defined"
  [^Class protocol-class]
  (let [segments (re-seq #"[^\.]+" (.getName protocol-class))
        ns-name (->> segments butlast (str/join "."))]
    (when-let [ns (get (munged-namespaces) ns-name)]
      (.name ^Namespace ns))))

(s/fdef protocol-name :args (s/cat :class class?) :ret string?)
(defn protocol-name
  "Return simple name of the protocol"
  [^Class protocol-class]
  (->> protocol-class
       (.getName)
       (re-seq #"[^\.]+")
       last
       symbol))

(s/fdef resolve-protocol :args (s/cat :cls class?) :ret (s/nilable var?))
(defn resolve-class->protocol
  "If this class is a protocol, return it"
  [cls]
  (let [ns-name (protocol-ns cls)
        name (protocol-name cls)]
    (when-let [v (and ns-name (ns-resolve ns-name name))]
      (when (protocol? @v)
        v))))

(s/fdef class-is-protocol? :args (s/cat :cls class?) :ret boolean?)
(defn class-is-protocol?
  "True if this class is a protocol"
  [cls]
  (boolean (resolve-class->protocol cls)))

(s/fdef unknown-method-spec :args (s/cat :record class? :protocol-class class? :protocol-method symbol? :params ::ana.jvm/bindings) :ret c/fn-spec?)
(defn protocol-unknown-method-spec
  "Create the unknown spec for a protocol method implementation (containing `this`). record is the class the protocol is being extended to. "
  [record protocol-class protocol-method params]
  (let [m (->> protocol-class
              (clojure.reflect/reflect)
              :members
              (filter (fn [m]
                        (= (munge protocol-method) (:name m))))
              (filter (fn [m]
                        (= (count (:parameter-types m)) (count params))))
              first)]
    (when-not m
      (println "unknown method spec:" protocol-class protocol-method params))
    (assert m)
    (c/fn-spec (c/cat- (vec (concat [(c/class-spec record)] (take (count (:parameter-types m)) (repeat (c/unknown {:message "no spec for protocol fn" protocol-class protocol-method}))))))
               (c/pred-spec #'any?)
               nil)))

(s/fdef protocol-fn-spec* :args (s/cat :cls class? :method symbol?) :ret (s/nilable c/fn-spec?))
(defn protocol-fn-spec*
  "Given a java class and method, return the spec for the protocol fn or nil"
  [cls method]
  (when-let [p (resolve-class->protocol cls)]
    (let [ns (protocol-ns cls)
          spec (s/get-spec (symbol (name ns) (name method)))]
      (when spec
        (c/parse-spec spec)))))

(s/fdef protocol-fn-spec :args (s/cat :record class? :protocol-class class? :protocol-method symbol? :params ::ana.jvm/bindings) :ret c/fn-spec?)
(defn protocol-fn-spec
  "Given a java class and method, return the spec for the protocol fn, otherwise return a spec consisting of 'unknown if not found"
  [record protocol-class protocol-method params]
  (or (protocol-fn-spec* protocol-class protocol-method)
      (protocol-unknown-method-spec record protocol-class protocol-method params)))

(defn flow-deftype-method-params [a path])

(s/fdef with-this-spec :args (s/cat :this-spec c/spect? :args c/spect?) :ret c/spect?)
(defn with-this-spec
  "Given a deftype and the spec for a java method call, prepend the `this` spec to :args, so it matches the deftype/defrecord method parameters"
  [java-args-spec this-spec]
  (assert (c/cat-spec? java-args-spec))
  (let [spec java-args-spec
        spec (update-in spec [:ps] (fn [ps]
                                     (vec (concat [this-spec] ps))))
        spec (if (:ks spec)
               (-> spec
                   (update-in [:ks] (fn [ks]
                                      (vec (concat [:this] ks))))
                   (update-in [:forms] (fn [forms]
                                         (vec (concat ['this] forms)))))
               spec)]
    spec))

(s/fdef deftype-interface-spec :args (s/cat :record class? :interface class? :method symbol? :params ::ana.jvm/bindings) :ret c/spect?)
(defn deftype-interface-spec
  "Given a deftype extending a java interface, return the spec for the method params"
  [record interface method params]
  (let [params (map (fn [p] (assoc p ::ret-spec (c/unknown {:message "any"}))) params)
        java-spec (get-java-method-spec interface method (analysis-args->spec params))
        _ (assert (c/fn-spec? java-spec))
        _ (assert (:args java-spec))]
    (update-in java-spec [:args] with-this-spec (c/class-spec record))))

(defn defmethod-get-spec
  "Given a record implementing a protocol/interface, return the spec for the method"
  [record interface method params]
  (assert (class? record))
  (assert (class? interface))
  (assert (symbol? method))
  (cond
    (class-is-protocol? interface) (protocol-fn-spec record interface method params)
    :else (deftype-interface-spec record interface method params)))

(defmethod flow* :method [a path]
  ;; deftype method
  (let [a* (get-in a path)
        ;;unknown-signature
        {:keys [interface name params]} a*
        method name
        record (-> a* :this :tag)
        spec (defmethod-get-spec record interface method params)
        params (vec (concat [(:this a*)] params))
        _ (assert (c/spect? spec))
        _ (assert (:args spec))
        params (destructure-fn-params params (:args spec))
        a (assoc-in a (conj path :params) params)
        ;;a (flow* a path)
        a (flow-walk a path)
        a* (get-in a path)
        body-ret-spec (strip-control-flow (::ret-spec (:body a*)))]
    (assoc-in a (conj path ::ret-spec) body-ret-spec)))

(defmethod flow* :vector [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (mapv ::ret-spec (:items a*))))))

(defmethod flow* :map [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        ret-keys (reduce (fn [ret-keys [k-a v-a]]
                           (let [k-s (::ret-spec k-a)]
                             (if (and (c/value? k-s) (keyword? (:v k-s)))
                               (let [key-type (if (qualified-keyword? (:v k-s))
                                                :req
                                                :req-un)]
                                 (assoc-in ret-keys [key-type (:v k-s)] (::ret-spec v-a)))
                               ret-keys))) {:req {}
                                            :req-un {}} (map vector (:keys a*) (:vals a*)))
        ret-spec (c/keys-spec (:req ret-keys) (:req-un ret-keys) {} {})]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :recur [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (recur-form (analysis-args->spec (:exprs a*))))))

(defmethod flow* :throw [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/unknown {:form {:exception (-> a* :exception :class :val)}
                                                   :message "form thows exception"}))))

(s/fdef keyword-invoke-ret-spec :args (s/cat :a ::analysis) :ret c/spect?)
(defn keyword-invoke-ret-spec
  [a]
  (let [spec (-> a :target ::ret-spec)
        k (-> a :keyword :val)]
    (assert k)
    (assert spec)
    (if (c/keyword-invoke? spec)
      (c/keyword-invoke spec (c/cat- [k]))
      (c/value nil))))

(defmethod flow* :keyword-invoke [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (keyword-invoke-ret-spec a*))))

(defmethod flow* :new [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/class-spec (-> a* :class :val)))))

(defmethod flow* :set! [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (::ret-spec (:val a*)))))

(defmethod flow* :set [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/coll-of (c/or- (map ::ret-spec (:items a*))) #{}))))

(defmethod flow* :case [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/or- (map ::ret-spec (:thens a*))))))

(defmethod flow* :case-test [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        ret-spec (-> a* :test ::ret-spec)]
    (when-not ret-spec
      (println "flow case-test:" a*))
    (assert ret-spec)
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :case-then [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :then ::ret-spec))))

(defmethod flow* :monitor-enter [a path]
  (assoc-in (flow-walk a path) (conj path ::ret-spec) (c/value nil)))

(defmethod flow* :monitor-exit [a path]
  (assoc-in (flow-walk a path) (conj path ::ret-spec) (c/value nil)))

(defmethod flow* :import [a path]
  (assoc-in (flow-walk a path) (conj path ::ret-spec) (c/class-spec Class)))

(defn get-java-field
  [class field & [{:keys [static?]}]]
  (some->> (reflect/reflect class)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Field m)
                           (if static?
                             (contains? (:flags m) :static)
                             true)
                           (= field (:name m)))))
           first))

(defmethod flow* :static-field [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        {:keys [field class]} a*]
    (let [f (get-java-field class field {:static? true})]
      (assoc-in a (conj path ::ret-spec) (resolve-java-class-spec (:type f))))))

(defmethod flow* :instance-field [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        {:keys [field class]} a*
        f (get-java-field class field)]
    (assoc-in a (conj path ::ret-spec) (resolve-java-class-spec (:type f)))))

(defmethod flow* :reify [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/and-spec (mapv c/class-spec (:interfaces a*))))))

(defmethod flow* :deftype [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/class-spec (:class-name a*)))))

(defmethod flow* :host-interop [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/unknown {:message "reflection, cannot be resolved at compile time"}))))

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
    (if (c/valid-invoke? s args)
      (if-let [a (data/get-var-analysis v)]
        (let [a (-> a :init :expr)]
          (if-let [method (get-fn-method-invoke a args)]
            (-> (flow-method* method args) ::ret-spec)
            (c/invalid {:form `(v ~args) :message (format "invoke args don't conform: %s %s" v args)})))
        (c/unknown {:form `(~v ~args) :message (format "var %s not analyzed" v)}))
      (c/invalid {:form `(~v ~args) :message (format "invoke-with-var does not conform: %s %s" v args)}))
    (c/unknown {:form `(v ~args) :message (format "invoke-with-var:" v "no spec")})))

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
  (let [a-args (:args a)
        args-spec (analysis-args->spec a-args)]
    (assert (:args s))
    (if (c/valid? (:args s) a-args)
      (if (:ret s)
        (:ret s)
        (c/unknown {:form (:form a) :a-loc (a-loc a) :message (format "no ret spec on %s" s)}))
      (c/invalid {:form (:form a)
                  :a-loc (a-loc a)
                  :message (format "invoke of %s does not conform. expected %s, got %s. " v (print-str (-> s :args)) (print-str args-spec))} a))))

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

(declare infer-walk)

(defn infer-wrap [a path]
  (let [a* (get-in a path)]
    (when-not a*
      (println "infer-wrap fail:" path))
    (assert a*)
    (binding [*a* a*]
      (let [a-post (infer* a path)
            a-post (if (::ret-spec (get-in a-post path))
                     a-post
                     (assoc-in a-post (conj path ::ret-spec) (c/unknown {:message (format "infer walk %s todo" (get-in a (conj path :op)))})))]
        (assert (::ret-spec (get-in a-post path)))
        a-post))))

(defn infer-walk
  ([a path]
   (infer-walk a path (get-in a (conj path :children))))
  ([a path children]
   (reduce (fn [a c]
             (if (contains? (get-in a path) c)
               (let [new-path (conj path c)
                     c-node (get-in a new-path)]
                 (if (sequential? c-node)
                   (reduce (fn [a i]
                             (infer-wrap a (conj new-path i))) a (range (count c-node)))
                   (infer-wrap a new-path)))
               a)) a (get-in a (conj path :children)))))

(defmethod infer* :default [a path]
  (println "infer* :default" (:op (get-in a path)))
  (infer-walk a path))

(defmethod infer* :const [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:val a*)))))

(defmethod infer* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/pred-spec #'var?))))

(defmethod infer* :var [a path]
  ;; :var => the value the var holds
  (let [a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (if-let [s (c/get-var-fn-spec v)]
                   s
                   (if-let [a (data/get-var-analysis v)]
                     (infer a)
                     (c/value @(:var a*))))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :the-var [a path]
  ;; the-var => (var foo). Returns the actual var
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:var a*)))))

(defmethod infer* :invoke [a path]
  (let [a (infer-walk a path [:args])
        a* (get-in a path)
        f-a (invoke-get-fn-analysis a path)
        s (invoke-get-fn-spec (:fn a*))
        args (:args a*)
        _ (println "infer* invoke:" (:form a*) args)
        a (if (and s (:args s))
            (reduce (fn [a arg]
                      (case (:op arg)
                        (:binding :local) (let [b (find-binding a path (:name arg))
                                                b-path (:path b)]
                                            (assert b-path)
                                            (infer-add-constraint a b-path (::ret-spec arg)))
                        (:const :invoke) a)) a args)
            a)
        ret-spec (if (and s (:ret s))
                   (:ret s)
                   (c/unknown {:message (format "no ret spec for %s" (:fn a*))}))]

    (assoc-in a (conj path ::ret-spec)
              (if (and s (:ret s))
                (:ret s)
                (c/unknown {:message (format "no ret spec on %s" (:form f-a))})))))

(defmethod infer* :static-call [a path]
  (let [a (infer-walk a path [:args])
        a* (get-in a path)
        {:keys [class method args]} a*
        ms (get-compatible-java-methods class method (analysis-args->spec args))
        ret-spec (->> ms
                      (map :return-type)
                      (map j/resolve-java-class)
                      (c/or-))
        a (assoc-in a (conj path ::ret-spec) ret-spec)
        method-specs (->> ms
                          (map :parameter-types)
                          (map (fn [params]
                                 (mapv (fn [p]
                                         (c/class-spec (j/resolve-java-class p))) params)))
                          (mapv c/or-))
        bind-args (map vector args method-specs)]
    (reduce (fn [a [arg method-spec]]
              (case (:op arg)
                (:local) (let [b (find-binding a path (:name arg))
                               b-path (:path b)]
                           (assert b-path)
                           (assert (c/spect? method-spec))
                           (infer-add-constraint a b-path method-spec))
                (:const :invoke) a)) a bind-args)))

(defmethod infer* :local [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        b (find-binding a path (:name a*))]
    (assert b (format "infer :local: failed to find binding: %s %s %s %s" (:name a*) (:form a*) (a-loc-str a*) (get-in a (pop (pop (pop (pop path)))))))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (c/spect? (::ret-spec b)))
    (assoc-in a (conj path ::ret-spec) (::ret-spec b))))

(defmethod infer* :fn [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        args (map (fn [m]
                    (c/cat- (mapv ::ret-spec (:params m)))) (:methods a*))
        rets (map (fn [m]
                    (::ret-spec (:body m))) (:methods a*))
        spec (c/fn-spec (c/or- args) (c/or- rets) nil)]
    (println "infer :fn" (:form a*) spec)
    (assoc-in a (conj path ::ret-spec) spec)))

(defmethod infer* :fn-method [a path]
  (let [a* (get-in a path)
        params (mapv (fn [p] (assoc p ::ret-spec (c/pred-spec #'any?))) (:params a*))
        a (assoc-in a (conj path :params) params)
        a (infer-walk a path)
        a* (get-in a path)]
    a))

(defmethod infer* :binding [a path]
  (let [a* (get-in a path)]
    (infer-walk a path)))

(defn infer-loop-let [a path]
  {:post [(spect-or-control-flow? (::ret-spec (get-in % path)))]}
  (let [a* (get-in a path)
        a (infer-walk a path)
        a* (get-in a path)
        ret-spec (::ret-spec (:body a*))]
    (assert ret-spec)
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :let [a path]
  (infer-loop-let a path))

(defmethod infer* :loop [a path]
  (infer-loop-let a path))

(defn print-walk-dispatch [a]
  (:op a))

(defmulti print-walk #'print-walk-dispatch)

(defmethod print-walk :default [a]
  (println (:form a) "=>" (::ret-spec a))
  (doseq [c (:children a)
          :let [node (get a c)]]
    (println (:op a) c)
    (if (sequential? node)
      (doseq [node* node]
        (print-walk node*))
      (print-walk node))))
