(ns spectrum.flow
  (:require [clojure.core.memoize :as memo]
            [clojure.core.match :refer [match]]
            [clojure.data :refer [diff]]
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
            [spectrum.util :as util :refer [print-once protocol? namespace? queue validate!]])
  (:import [clojure.lang Var Namespace]))

(declare find-binding)

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(s/def ::args-spec ::c/spect-like)
(s/def ::ret-spec ::c/spect-like)

(s/def ::var (s/with-gen (s/spec var?)
               (fn []
                 (gen/elements [#'int? #'println #'str]))))

(s/def ::analysis (s/merge ::ana.jvm/analysis (s/keys :opt [::var ::args-spec ::ret-spec])))

(s/def ::analysis? (s/nilable ::analysis))

(s/def ::analyses (s/coll-of ::analysis))
(s/def ::path-elem (s/or :k keyword? :i nat-int?))
(s/def ::path (s/coll-of ::path-elem :type vector?))

(s/fdef a-loc :args (s/cat :a ::ana.jvm/analysis) :ret (s/keys :opt-un [:ana.jvm.env/file :ana.jvm.env/line :ana.jvm.env/column]))
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

(s/fdef maybe-strip-meta :args (s/cat :a (s/nilable ::ana.jvm/analysis)) :ret ::ana.jvm/analysis)
(defn maybe-strip-meta
  "If a is a :op :with-meta, strip it and return the :expr, or a"
  [a]
  (if (-> a :op (= :with-meta))
    (-> a :expr)
    a))

(defn infer-dispatch [a path]
  (-> a (get-in path) :op))

(defmulti infer* #'infer-dispatch)

(defn infer-result [a]
  (cond
    (= :def (:op a)) (println (-> a :var) "=>" (-> a :init maybe-strip-meta ::ret-spec))
    :else (println (:form a) "=>" (::ret-spec a))))

(defn infer-
  "Given an un-spec'd analysis, return our best guess for the spec"
  [a]
  (let [a* (infer* a [])]
    (infer-result a*)
    a*))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis) :ret ::analysis)
(def infer (memo/memo infer-))

(s/fdef infer-var :args (s/cat :a ::ana.jvm/analysis :v var?) :ret c/spect?)
(defn infer-var
  "Given the analysis for a def, infer and return the var value"
  [a v]
  {:pre [(var? v)]
   :post [(s/valid? c/spect? %)]}
  (infer a)
  (or (data/get-var-inferred-spec v)
      (c/value nil)))

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
  (let [a* (get-in a path)]
    (try
      (assert a*)
      (binding [*a* a*]
        (let [a* (get-in a path)
              _ (assert a*)
              a (flow* a path)
              a* (get-in a path)]
          (when-not (s/valid? ::c/spect-like (::ret-spec a*))
            (println "walk failed:" (:form a*) "=>" (::ret-spec a*)))
          (validate! ::c/spect-like (::ret-spec a*))
          a))
      (catch Throwable t
        (println "flow-walk exception while walking:" (.getMessage t) (a-loc-str a*) (:op a*) (:form a*))
        (throw t)))))

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
  a)

(defn get-var-spec [v]
  (or (c/get-var-spec v)
      (data/get-var-inferred-spec v)))

(defmethod flow* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)]
    (assert (var? v))
    (data/store-var-analysis a)
    (when-not (get-var-spec v)
      (infer a))
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
        ret-spec (if-let [s (get-var-spec v)]
                   s
                   (if-let [a (data/get-var-analysis v)]
                     (c/spec-spec (s/spec v))
                     (c/value @(:var a*))))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :with-meta [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (::ret-spec (:expr a*)))))

(defmethod flow* :fn [a path]
  (let [;;a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        fn-spec (when v get-var-spec)
        a (if fn-spec
            (flow-walk a path)
            (infer* a path))
        a* (get-in a path)
        ret-spec (::ret-spec a*)]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defn find-binding*-dispatch [a name]
  (assert (:op a))
  (assert name)
  (:op a))

(defmulti find-binding* #'find-binding*-dispatch)

(defmethod find-binding* :default [a name]
  nil)

(defn find-binding-let [a name]
  (some->> a
           :bindings
           (map-indexed (fn [i b]
                          (assoc b :index i)))
           (filter (fn [b] (= name (:name b))))
           first
           (#(assoc % :path [:bindings (:index %)]))))

(defmethod find-binding* :let [a name]
  (find-binding-let a name))

(defmethod find-binding* :letfn [a name]
  (find-binding-let a name))

(defmethod find-binding* :loop [a name]
  (find-binding-let a name))

(defmethod find-binding* :local [a name]
  (when (and (= (:name a) name) (::ret-spec a))
    a))

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
    (assoc (:local a) :path [:local])))

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
    (c/and-spec? s) (c/and-conj s (c/not- x))
    :else (c/and- [(maybe-disj-pred s x) (c/not- x)])))

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
                                          :pred (c/and- [spec test-pred])
                                          :nil (c/value nil)
                                          :truthy (-> spec (and-not (c/pred-spec #'nil?)) (and-not (c/pred-spec #'false?)))
                                          :instance? (c/and- [spec (c/class-spec (:class test))]))
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

(s/fdef infer-add-constraint :args (s/cat :a ::analysis :b-path vector? :method-spec c/spect?))
(defn infer-add-constraint [a b-path method-spec]
  (let [b (get-in a b-path)]
    (assert b (format "binding not found: %s %s" (:form a) b-path))
    (assert b-path)
    (assert (::ret-spec b) (format "no ret-spec on %s %s %s" (:op b) (:form b) (a-loc-str a)))
    (update-in a (conj b-path ::ret-spec) c/add-constraint method-spec)))

(defn infer-or-constraint [a b-path constraint]
  (let [b (get-in a b-path)]
    (assert b (format "binding not found: %s %s" (:form a) b-path))
    (assert b-path)
    (assert (::ret-spec b) (format "no ret-spec on %s %s %s %s" (:name b) (keys b) (:op b) (a-loc-str a)))
    (update-in a (conj b-path ::ret-spec) c/add-or-constraint constraint)))

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
      :const (-> a* :fn :val)
      :invoke (recur a (conj path :fn))
      (println "don't know how to find analysis for" fn-op))))

(s/fdef invoke-get-fn-spec :args (s/cat :a ::analysis :p ::path) :ret (s/nilable ::c/spect))

(defn invoke-get-fn-spec-dispatch [a path]
  (-> (get-in a path) :op))

(defmulti invoke-get-fn-spec "Given the :fn from an :invoke a, return the spec for the thing being invoked"
  #'invoke-get-fn-spec-dispatch)

(defmethod invoke-get-fn-spec :var [a path]
  {:post [(or (nil? %) (c/spect? %))]}
  (let [a* (get-in a path)
        v (-> a* :var)]
    (assert (var? v))
    (if-let [s (get-var-spec v)]
      s
      (if-let [v-a (data/get-var-analysis v)]
        (c/spec-spec v)
        (do
          (println "invoke-get-fn-spec:" (:form a*) v)
          (assert false (format "couldn't find spec or analysis for %s" v))
          (c/unknown {:message (format "couldn't find spec or analysis for %s" v)}))))))

(defmethod invoke-get-fn-spec :local [a path]
  (let [a* (get-in a path)]
    (assert (:name a*))
    (-> (find-binding a path (:name a*)) ::ret-spec)))

(defmethod invoke-get-fn-spec :default [a path]
  (let [a* (get-in a path)]
    (c/unknown {:message (format "don't know how to get spec or analysis for %s %s" (:op a*) (:form a*))})))

(defn contains-control-flow? [s]
  (if (c/compound-spec? s)
    (->> s
         (c/map* contains-control-flow?)
         (some identity))
    (c/control-flow? s)))

(s/fdef strip-control-flow :args (s/cat :s (s/nilable c/spect?)) :ret (s/nilable c/spect?))
(defn strip-control-flow
  "Given the ret-spec for a function, remove control flow (recur and throw) from the type."
  [s]
  (if (c/compound-spec? s)
    (->> s
         (c/filter* (fn [p] (not (c/control-flow? p))))
         (map strip-control-flow)
         ((fn [ps]
            (if (seq ps)
              (c/new- s ps)
              (c/invalid {:message (format "control flow in both branches: %s" (print-str s))})))))
    s))

(defmethod flow* :invoke [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        fn-spec (-> a* :fn ::ret-spec)
        args-spec (analysis-args->spec (:args a*))
        arg-count (count (:args a*))
        f-a (invoke-get-fn-analysis a path)
        fn-spec (if fn-spec
                  fn-spec
                  (when f-a
                    (assert false)))]
    (try
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
        (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "invoke: wrong number of args %s" (:form a*))})))
      (catch Exception e
        (println e "flow :invoke while walking:" (:form a*) (a-loc-str a))
        (throw e)))))

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
               (get-var-spec v))
        a (flow-walk a path)
        a* (get-in a path)
        args-spec (analysis-args->spec (:args a*))]
    (assoc-in a (conj path ::ret-spec) (if spec
                                         (c/invoke spec args-spec)
                                         (c/unknown {:message (format "protocol-invoke: no spec for %s" (:var (:fn a)))})))))


(defn walk-if [walk-fn a path]
  (let [a (walk-fn a path)
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
                                         :ambiguous (c/or- [then-ret-spec
                                                            else-ret-spec])))))
(defmethod flow* :if [a path]
  (walk-if flow-walk a path))

(defmethod flow* :const [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:val a*)))))

(defmethod flow* :do [a path]
  (let [a (flow-walk a path)]
    (assoc-in a (conj path ::ret-spec) (-> a (get-in path) :ret ::ret-spec))))

(defn walk-catch [walk-fn a path]
  {:post [(s/valid? ::analysis (get-in % path))]}
  (let [a (walk-fn a path)
        a* (get-in a path)]
    (assert (or (map? (:body a*)) (nil? (:body a*))))
    (assoc-in a (conj path ::ret-spec) (if (:body a*)
                                         (-> a* :body ::ret-spec)
                                         (c/value nil)))))

(defmethod flow* :catch [a path]
  (walk-catch flow-walk a path))

(defn walk-try [walk-fn a path]
  {:post [(s/valid? ::analysis (get-in % path))]}
  (let [a (walk-fn a path)
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

(defmethod flow* :try [a path]
  (walk-try flow-walk a path))

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
    (if (and (c/first- arg-spec)
             (c/first- method-spec))
      (let [m (c/first- method-spec)
            m-c (c/spec->classes m)
            _ (assert (= 1 (count m-c)))
            m-c (first m-c)
            a (c/first- arg-spec)
            a-c (c/spec->classes a)]
        (if (and (nil? a) (nil? m))
          true
          (if (and m a (or (c/valid? m a)
                           (when (and m-c (seq a-c))
                             (every? (fn [a-c*]
                                       (j/castable? m-c a-c*)) a-c))
                           (c/unknown? a)))
            (recur (c/rest- arg-spec) (c/rest- method-spec))
            false)))
      (if (and (nil? (c/first- arg-spec))
               (nil? (c/first- method-spec)))
        true
        false))))

(s/fdef compatible-java-method? :args (s/cat :v ::c/spect :method-types (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
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
  (let [s (c/first- spec)
        arg (first arg-vec)]
    (if (and s arg)
      (if (c/known? s)
        (let [cs (c/spec->classes s)
              arg (j/resolve-java-class arg)]
          (if (and cs arg (some (fn [c*]
                                 (j/narrowing? c* arg)) cs))
            true
            (recur (c/rest- spec) (rest arg-vec))))
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
        a (maybe-flow-multi-method a)]
    (if (and class method)
      (let [args-spec (analysis-args->spec (util/zip a :args))
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
            (assoc a ::ret-spec spec))))
      (assoc a ::ret-spec (c/unknown {:message (format "no spec on reflection: %s" (:form a))})))))

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
  (let [a* (get-in a path)
        a (flow-walk a path)
        a* (get-in a path)
        ret-spec (::ret-spec (:body a*))]
    (assert ret-spec)
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :let [a path]
  (flow-loop-let a path))

(defn find-loop
  "Given a recur, find the enclosing loop. returns the path"
  [a path]
  (loop [path path]
    (let [a* (get-in a path)]
      (if (contains? #{:loop :fn-method} (:op a*))
        path
        (if (seq path)
          (recur (pop path))
          (assert false (format "couldn't find loop in %s" (:form a))))))))

(defmethod flow* :loop [a path]
  {:post [(not (contains-control-flow? %))]}
  (let [a (flow-loop-let a path)
        a* (get-in a path)]
    (update-in a (conj path ::ret-spec) (fn [s]
                                          (strip-control-flow s)))))

(defn walk-recur [walk-fn a path]
  (let [a (walk-fn a path)
        a* (get-in a path)
        loop-path (find-loop a path)
        loop (get-in a loop-path)
        loop-specs (map ::ret-spec (or (:bindings loop) (:params loop)))
        loop-arg-count (count loop-specs)
        recur-specs (map ::ret-spec (:exprs a*))
        recur-arg-count (count recur-specs)]
    (if (= loop-arg-count recur-arg-count)
      (let [a (assoc-in a (conj path ::ret-spec) (c/recur-form (analysis-args->spec (:exprs a*))))
            loop-specs* (map (fn [l r] (if (and (c/conformy? l) (c/conformy? r))
                                         (c/or- [l r])
                                         (first (remove c/conformy? [l r])))) loop-specs recur-specs)]
        (if (::walked? a*)
          a
          (let [bindings-key (if (:bindings loop)
                               :bindings
                               :params)
                a (update-in a (conj loop-path bindings-key) (fn [bindings]
                                                               (mapv (fn [b s]
                                                                       (assoc b ::ret-spec s)) bindings loop-specs*)))]
            (walk-fn (assoc-in a (conj path ::walked?) true) loop-path))))
      (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "recur bad arity, loop takes %s args, got %s" loop-arg-count recur-arg-count)})))))

(defmethod flow* :recur [a path]
  (walk-recur flow-walk a path))

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
          (if (and (first params) (c/first- args))
            (let [params* (rest params)
                  args* (c/rest- args)]
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
        (let [spec* (c/rest- spec)
              args* (seq (rest args))]
          (if (and spec* args*)
            (recur spec* args*)
            (if (and (nil? args*) (or (nil? spec*) (c/accept-nil? spec*)))
              true
              false)))))
    false))

(def macro-form-spec (c/pred-spec #'any?))
(def macro-env-spec (c/or- [(c/map-of (c/pred-spec #'symbol?) (c/class-spec clojure.lang.Compiler$LocalBinding)) (c/value nil)]))

(s/fdef destructure-fn-params :args (s/cat :params ::ana.jvm/bindings :spec ::c/spect :macro? (s/? boolean?)) :ret ::ana.jvm/bindings)
(defn destructure-fn-params
  "Given a spect and ana.jvm/fn-method params, update params to include spec"
  ([params spec macro?]
   {:post [(every? (fn [p] (c/spect? (::ret-spec p))) %)
           (= (count params) (count %))]}
   (let [ret (if macro?
               [(assoc (first params) ::ret-spec macro-form-spec) (assoc (second params) ::ret-spec macro-env-spec)]
               [])
         params-original params
         params (if macro?
                  (vec (drop 2 params))
                  params)]
     (if (arity-conform? spec params)
       (loop [ret ret
              params params
              spec spec]
         (if (and (seq params)
                  spec)
           (let [param (first params)
                 ss (c/will-accept spec)
                 s (c/or- ss)]
             (assert (c/spect? s))
             (if (:variadic? param)
               (conj ret (assoc param ::ret-spec spec))
               (recur (conj ret (assoc param ::ret-spec s)) (rest params) (c/rest- spec))))
           ret))
       (mapv (fn [p]
               (assoc p ::ret-spec (c/invalid {:form (:name p) :message "destructure failed"}))) params-original))))
  ([params spec]
   (destructure-fn-params params spec false)))

(s/fdef macro? :args (s/cat :a ::ana.jvm/analysis) :ret boolean?)
(defn macro?
  "True if this analysis is in a macro definition (top level of the form is :def, and the var is a macro)"
  [a]
  (match a
    {:op :do :statements ([{:op :def :var (_ :guard #(-> % meta :macro))} & rest] :seq)} true
    :else false))

(s/fdef flow-method* :args (s/cat :a ::analysis :path vector? :args (s/nilable c/spect?)))
(defn flow-method* [a path args-spec]
  (let [a* (get-in a path)
        a (if args-spec
            (update-in a (conj path :params) destructure-fn-params args-spec (macro? a))
            (do
              (println "flow-method: no spec for" (:form (get-in a (pop (pop path)))))
              (assert false)
              ;; (update-in a (conj path :params) (fn [params]
              ;;                                    (mapv (fn [p]
              ;;                                            (assoc p ::ret-spec (c/unknown {:message (format "method params: no spec for %s" (:form (get-in a (pop path)))) :form (:name p) :a-loc (a-loc a*)}))) params)))
              ))
        a (flow* a (conj path :body))
        body (get-in a (conj (conj path :body)))
        body-ret-spec (strip-control-flow (::ret-spec body))]
    (validate! ::c/spect-like body-ret-spec)
    (assoc-in a (conj path ::ret-spec) body-ret-spec)))

(defn flow-method [a path]
  (let [a* (get-in a path)
        v (some-> a (get-in (pop (pop path))) ::var)
        s (some-> v get-var-spec)
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

(defn walk-map [walk-fn a path]
  (let [a (walk-fn a path)
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

(defmethod flow* :map [a path]
  (walk-map flow-walk a path))

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

(defn walk-instance-field [f a path]
  (let [a (f a path)
        a* (get-in a path)
        {:keys [field class]} a*
        f (get-java-field class field)]
    (assoc-in a (conj path ::ret-spec) (resolve-java-class-spec (:type f)))))

(defmethod flow* :instance-field [a path]
  (walk-instance-field flow-walk a path))

(defn walk-reify [f a path]
  (let [a* (get-in a path)
        a (assoc-in a (conj path ::ret-spec) (c/and- (mapv c/class-spec (:interfaces a*))))]
    (f a path)))

(defmethod flow* :reify [a path]
  (walk-reify flow-walk a path))

(defn walk-deftype [f a path]
  (let [a* (get-in a path)
        a (assoc-in a (conj path ::ret-spec) (c/class-spec (:class-name a*)))]
    (f a path)))

(defmethod flow* :deftype [a path]
  (walk-deftype flow-walk a path))

(defn walk-host-interop [f a path]
  (let [a (f a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/unknown {:message "reflection, cannot be resolved at compile time"}))))

(defmethod flow* :host-interop [a path]
  (walk-host-interop flow-walk a path))

(defmethod flow* :letfn [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :body ::ret-spec))))

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
  (if-let [s (get-var-spec v)]
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
      (println "infer-wrap fail:" path (:form (get-in a (pop (pop (pop path))))) (a-loc-str a)))
    (assert a*)
    (binding [*a* a*]
      (let [a-post (infer* a path)
            a*-post (get-in a-post path)
            _ (when-not (s/valid? ::analysis a-post)
                (println "infer-wrap invalid:" (:op (get-in a path)) ))
            a-post (if (::ret-spec (get-in a-post path))
                     a-post
                     (assert false (format "no ::ret-spec on %s %s" (:op (get-in a-post path)) (:form (get-in a-post path)))))]
        (assert (::ret-spec (get-in a-post path)))
        a-post))))

(defn infer-walk
  ([a path]
   (infer-walk a path (get-in a (conj path :children))))
  ([a path children]
   (if (seq children)
     (reduce (fn [a c]
               (if (contains? (get-in a path) c)
                 (let [new-path (conj path c)
                       c-node (get-in a new-path)]
                   (if (sequential? c-node)
                     (reduce (fn [a i]
                               (let [new-a (infer-wrap a (conj new-path i))]
                                 (assert (pos? (count (get-in a new-path))))
                                 (assert (= (count (get-in a new-path)) (count (get-in new-a new-path))))
                                 new-a)) a (range (count c-node)))
                     (infer-wrap a new-path)))
                 a)) a (get-in a (conj path :children)))
     a)))

(defmethod infer* :default [a path]
  (println "infer* :default" (:op (get-in a path)))
  (assert false (format "unhandled: infer %s" (:op (get-in a path))))
  (infer-walk a path))

(defmethod infer* :const [a path]
  (let [a* (get-in a path)
        a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:val a*)))))

(defn recursive?
  "True if path is a :var analysis inside it's own :def"
  [a path]
  {:pre [a]}
  (let [a* (get-in a path)
        a*-var (:var a*)]
    (assert a*)
    (assert (:op a*))
    (assert (var? a*-var))
    (when (and (= :var (:op a*)) (seq path))
      (loop [path* (pop path)]
        (let [x (get-in a path*)]
          (if (and (= :def (:op x)) (= a*-var (:var x)))
            true
            (if (seq path*)
              (recur (pop path*))
              false)))))))

(defmethod infer* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        a (infer-walk a path)
        a* (get-in a path)]
    (when-let [s (-> a* :init ::ret-spec)]
      (println "infer :def storing" (-> a* :var) "=>" s)
      (data/store-var-inferred-spec (-> a* :var) s))
    (assoc-in a (conj path ::ret-spec) (c/pred-spec #'var?))))

(defmethod infer* :var [a path]
  ;; :var => the value the var holds
  (let [a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (if-let [s (get-var-spec v)]
                   s
                   (if-let [v-a (data/get-var-analysis v)]
                     (c/spec-spec (s/spec v))
                     (c/value @(:var a*))))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :the-var [a path]
  ;; the-var => (var foo). Returns the actual var
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:var a*)))))

(defn infer-invoke-constraint- [queue]
  (let [q (first queue)
        {:keys [spec args ret]} q
        qr (rest queue)
        [a & ar] args]
    (if q
      (if (and a spec (c/conformy? spec))
        (let [wa (c/will-accept spec)
              was (filter (fn [wa]
                            (c/non-contradiction? a wa)) wa)]
          (if (seq was)
            (lazy-cat (infer-invoke-constraint- (concat qr (->> was
                                                                    (map (fn [wa]
                                                                           (let [s-next (c/derivative spec wa)]
                                                                             (when (c/conformy? s-next)
                                                                               {:spec s-next
                                                                                :args ar
                                                                                :ret (conj ret wa)}))))
                                                                    (filter identity)))))
            (infer-invoke-constraint- qr)))
        (if (and (not a) (c/accept-nil? spec))
          (lazy-cat [ret] (infer-invoke-constraint- qr))
          (do
            (infer-invoke-constraint- qr))))
      nil)))

(s/fdef infer-invoke-constraints :args (s/cat :s c/spect? :args (s/coll-of c/spect?) :ret c/spect?))
(defn infer-invoke-constraints
  "Given a spec (which could accept multiple type or arities), and a
  set of partially constrained argument specs, return a spec
  representing all possible variations of spec that args could conform
  to"
  [spec args]
  (let [rets (infer-invoke-constraint- (queue [{:spec spec
                                                :args args
                                                :ret []}]))]
    (if (seq rets)
      (let [_ (assert (every? (fn [r]
                                (= (count args) (count r))) rets))
            constraints (apply map (fn [& rs]
                                     (c/or- rs)) rets)
            _ (assert (= (count constraints) (count args)))]
        constraints)
      (take (count args) (repeat (c/invalid {:message (format "can't invoke %s with %s" (print-str spec) (print-str args))}))))))

(defmethod infer* :invoke [a path]
  (let [a-orig a
        a* (get-in a path)
        a (infer-walk a path [:args])
        a* (get-in a path)
        f-a (invoke-get-fn-analysis a path)
        invoke-var? (boolean (get-in a (concat path [:fn :var])))
        recursive (and invoke-var? (recursive? a (conj path :fn)))
        s (when-not recursive
            (invoke-get-fn-spec a (conj path :fn)))]
    (if s
      (if (c/invoke? s)
        (let [a-args (:args a*)
              s-args (c/invoke-accept s)
              s-args (infer-invoke-constraints s-args (map ::ret-spec a-args))
              args (map vector a-args s-args)
              a (if s-args
                  (reduce (fn [a [a-arg s-arg]]
                            (case (:op a-arg)
                              (:binding :local) (let [b (find-binding a path (:name a-arg))
                                                      b-path (:path b)]
                                                  (assert b-path)
                                                  (infer-add-constraint a b-path s-arg))
                              a)) a args)
                  a)
              a-args-s (c/cat- (map ::ret-spec a-args))

              ;; if the inferred args are more specific than what the spec takes, the return type could be useful
              invoke-args (if (c/valid? (c/cat- s-args) a-args-s )
                            a-args-s
                            (c/invoke-accept s))
              _ (println "infer invoke" s "w/" invoke-args)
              ret-spec (c/invoke s invoke-args)]
          (assoc-in a (conj path ::ret-spec) ret-spec))
        (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "infer invoke: can't invoke %s" (print-str s))})))
      (do
        (if recursive
          (assoc-in a (conj path ::ret-spec) (c/unknown {:message "TODO self-recursion"}))
          (assert false "no spec found while inferring"))))))

(defmethod infer* :static-call [a path]
  (let [a (infer-walk a path [:args])
        a* (get-in a path)
        {:keys [class method args]} a*
        ms (->> (get-java-method class method)
                     (filter (fn [m]
                               (= (count (:parameter-types m))
                                  (count args)))))
        ret-spec (if (seq ms)
                   (->> ms
                        (map :return-type)
                        (map j/resolve-java-class)
                        (map c/class-spec)
                        (c/or-))
                   (c/invalid {:message (format "no compatible method method: on %s %s accepts %s" class method (print-str (analysis-args->spec args)))}))
        a (assoc-in a (conj path ::ret-spec) ret-spec)
        method-spec (if (seq ms)
                      (->> ms
                           (map :parameter-types)
                           (map (fn [params]
                                  (mapv (fn [p]
                                          (c/class-spec (j/resolve-java-class p))) params)))
                           (apply map vector)
                           (map c/or-))
                       (c/invalid {:message (format "no compatible method method: on %s %s accepts %s" class method (print-str (analysis-args->spec args)))}))
        bind-args (map vector args method-spec)]
    (reduce (fn [a [arg method-spec]]
              (case (:op arg)
                (:local :binding) (let [b (find-binding a path (:name arg))
                                        b-path (:path b)]
                                    (assert b-path (format "couldn't find binding %s in %s" (:name arg) (:form a)))
                                    (assert (c/spect? method-spec))
                                    (infer-add-constraint a b-path method-spec))
                a)) a bind-args)))

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
  (let [a* (get-in a path)
        a (if (:local a*)
            ;; FIXME this local could be self-recursive, need complete spec here, but don't have it yet. Maybe re-flow after first infer pass?
            (assoc-in a (concat path [:local ::ret-spec]) (c/pred-spec #'fn?))
            a)
        a (assoc-in a (concat path [::ret-spec]) (c/pred-spec #'fn?))
        a (infer-walk a path)
        a* (get-in a path)
        args (->>
              (:methods a*)
              (map (fn [m]
                     (c/cat- (mapv ::ret-spec (:params m)))))
              (c/or-))
        rets (->>
              (:methods a*)
              (map (fn [m]
                     (::ret-spec (:body m))))
              (c/or-))
        spec (c/fn-spec args rets nil)]
    (assoc-in a (conj path ::ret-spec) spec)))

(defmethod infer* :fn-method [a path]
  (let [a* (get-in a path)
        params (mapv (fn [p]
                       (let [ret-spec (cond
                                        (:variadic? p) (c/and- [(c/seq-of (c/pred-spec #'any?)) (c/class-spec clojure.lang.ISeq)])
                                        (and (:tag p) (not= Object)) (c/class-spec (:tag p))
                                        :else (c/pred-spec #'any?))]
                         (assoc p ::ret-spec ret-spec))) (:params a*))
        a (assoc-in a (conj path :params) params)
        a (infer-walk a path)
        a* (get-in a path)
        a (assoc-in a (conj path ::ret-spec) (-> a* :body ::ret-spec))]
    a))

(defn find-this
  "In a reify/deftype/defrecord, walk up the `a` until we find the `this`, and return it"
  [a path]
  (let [a* (get-in a path)]
    (if (contains? #{:reify :deftype} (:op a*))
      a*
      (if (seq path)
        (recur a (pop path))
        (assert false (format "couldn't find `this` in %s" (:form a)))))))

(defmethod infer* :binding [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        a* (cond
             (:init a*) (assoc a* ::ret-spec (::ret-spec (:init a*)))
             (= :catch (:local a*)) (assoc a* ::ret-spec (c/class-spec (:tag a*)))
             (= :this (:local a*)) (let [this (find-this a path)
                                         ret-spec (::ret-spec this)]
                                     (assert (c/spect? ret-spec))
                                     (assoc a* ::ret-spec ret-spec))
             :else a*)]
    (when-not (::ret-spec a*)
      (println "binding fail:" (:op a*) a*)
      (println "infer* :binding fail" (:form a*) (a-loc-str a*))
      (println "infer* :binding local" (:local a*)))
    (assert (::ret-spec a*))
    (assoc-in a (conj path ::ret-spec) (::ret-spec a*))))

(defmethod infer* :do [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :ret ::ret-spec))))

(defmethod infer* :new [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        cls (-> a* :class :val)
        _ (assert (class? cls))
        constructors (-> cls
                         reflect/reflect
                         :members
                         (->>
                          (filter (fn [m]
                                    (and (instance? clojure.reflect.Constructor m)
                                         (= (count (:parameter-types m)) (count (:args a*))))))))
        constructor-specs (->> constructors
                               (map :parameter-types)
                               (map (fn [constructor-args]
                                      (mapv (fn [arg]
                                              (c/class-spec (j/resolve-java-class arg))) constructor-args)))
                               (apply map vector)
                               (map c/or-))
        a (reduce (fn [a [arg spec]]
                    (case (:op arg)
                      (:binding :local) (let [b (find-binding a path (:name arg))
                                              b-path (:path b)]
                                          (assert b-path)
                                          (assert (c/spect? spec))
                                          (infer-add-constraint a b-path spec))
                      a)) a (map vector (:args a*) constructor-specs))]
    (assoc-in a (conj path ::ret-spec) (c/class-spec (-> a* :class :val)))))

(defmethod infer* :with-meta [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :expr ::ret-spec))))

(defn infer-loop-let [a path]
  {:post [(c/spect-or-control-flow? (::ret-spec (get-in % path)))]}
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

(defn infer-java-call
  "Handles both :static-call and :instance-call"
  [a]
  {:post [(::ret-spec %)]}
  (let [{:keys [class method instance]} a
        a (maybe-flow-multi-method a)]
    (if (and class method)
      (let [args-spec (analysis-args->spec (util/zip a :args))
            meth (get-conforming-java-method class method args-spec)
            spec (get-java-method-spec class method args-spec)
            spec (if (and meth spec (c/known? (:args spec)))
                   (c/maybe-transform-method meth spec args-spec)
                   spec)]

        ;; TODO ADD CONSTRAINT
        (if (c/fn-spec? spec)
          (do
            (assert (:ret spec))
            (if (c/every-known? args-spec)
              (assoc a ::ret-spec (:ret spec) ::args-spec (:args spec))
              (assoc a ::ret-spec (c/unknown {:form (:form a) :message (format "invoke %s with unknown args %s" (print-str spec) (print-str args-spec))}))))
          (do
            (assert (c/invalid? spec))
            (assoc a ::ret-spec spec))))
      (assoc a ::ret-spec (c/unknown {:message (format "no spec on reflection: %s" (:form a))})))))

(defmethod infer* :instance-call [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        a* (infer-java-call a*)]
    (assoc-in a (conj path ::ret-spec) (::ret-spec (infer-java-call a*)))))

(defmethod infer* :if [a path]
  (walk-if infer-walk a path))

(defmethod infer* :recur [a path]
  (walk-recur infer-walk a path))

(defmethod infer* :catch [a path]
  (walk-catch infer-walk a path))

(defmethod infer* :try [a path]
  (walk-try infer-walk a path))

(defmethod infer* :map [a path]
  (walk-map infer-walk a path))

(defmethod infer* :static-field [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        {:keys [field class]} a*]
    (let [f (get-java-field class field {:static? true})]
      (assoc-in a (conj path ::ret-spec) (resolve-java-class-spec (:type f))))))

(defmethod infer* :quote [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :expr ::ret-spec))))

(defmethod infer* :import [a path]
  (assoc-in (infer-walk a path) (conj path ::ret-spec) (c/class-spec Class)))

(defmethod infer* :vector [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (mapv ::ret-spec (:items a*))))))

(defmethod infer* :set [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (if (seq (:items a*))
                                         (c/coll-of (c/or- (map ::ret-spec (:items a*))) #{})
                                         (c/value #{})))))

(defmethod infer* :throw [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        e (:exception a*)
        a (case (:op e)
            (:binding :local) (let [b (find-binding a path (:name e))
                                    b-path (:path b)]
                                (assert b-path)
                                (infer-add-constraint a b-path (::ret-spec e)))
            a)]
    (assoc-in a (conj path ::ret-spec) (c/throw-form (::ret-spec e)))))

(defmethod infer* :keyword-invoke [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (keyword-invoke-ret-spec a*))))

(defmethod infer* :instance? [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        s (c/class-spec (:class a*))
        arg-spec (-> a* :target ::ret-spec)
        ret-spec (c/pred-spec #'boolean?)]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :protocol-invoke [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        v (-> a* :fn :var)
        spec (when v
               (get-var-spec v))
        a-args (:args a*)
        s-args (when (and spec (:args spec))
                 ;; (c/all-possible-values-arity-n (:args spec) (count (:args a*)))
                 )
        args (map vector a-args s-args)
        a (if (and spec (:args spec))
            (reduce (fn [a [a s]]
                      (case (:op a)
                        (:binding :local) (let [b (find-binding a path (:name a))
                                                b-path (:path b)]
                                            (assert b-path)
                                            (println "protocol-invoke:" s (:name a) "=>" s)
                                            (infer-add-constraint a b-path s))
                        a)) a args)
            a)]
    (assoc-in a (conj path ::ret-spec) (if (and spec (:ret spec))
                                         (:ret spec)
                                         (c/unknown {:message (format "protocol-invoke: no spec for %s" (:var (:fn a)))})))))

(defmethod infer* :case [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        rets (map ::ret-spec (:thens a*))
        rets (if (:default a*)
               (do
                 (assert (-> a* :default ::ret-spec))
                 (conj rets (-> a* :default ::ret-spec)))
               rets)
        ret-spec (c/or- rets)]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :case-test [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assert (::ret-spec (:test a*)))
    (assoc-in a (conj path ::ret-spec) (::ret-spec (:test a*)))))

(defmethod infer* :case-then [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assert (::ret-spec (:then a*)))
    (assoc-in a (conj path ::ret-spec) (::ret-spec (:then a*)))))

(defmethod infer* :set! [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        a (assoc-in a (conj path ::ret-spec) (::ret-spec (:val a*)))]
    (case (:op (:target a*))
      (:binding :local) (let [b (find-binding a path (:name (:target a*)))
                              b-path (:path b)]
                          (assert b)
                          (assert b-path)
                          (infer-or-constraint a b-path (::ret-spec (:val a*))))
      a)))

(defmethod infer* :instance-field [a path]
  (walk-instance-field infer-walk a path))

(defmethod infer* :host-interop [a path]
  (walk-host-interop infer-walk a path))

(defmethod infer* :reify [a path]
  (walk-reify infer-walk a path))

(defn strip-this-arg
  "Remove the `this` arg from a params vec"
  [params]
  (filterv (fn [p]
             (when (not= :this (:local p))
               p)) params))

(defmethod infer* :method [a path]
  ;; deftype method
  (let [a* (get-in a path)
        ;;unknown-signature
        {:keys [interface name params]} a*
        method name
        record (-> a* :this :tag)
        params (strip-this-arg params)
        spec (defmethod-get-spec record interface method params)
        params (vec (concat [(:this a*)] params))
        _ (assert (c/spect? spec))
        _ (assert (:args spec))
        params (destructure-fn-params params (:args spec))
        a (assoc-in a (conj path :params) params)
        ;;a (flow* a path)
        a (infer-walk a path)
        a* (get-in a path)
        body-ret-spec (strip-control-flow (::ret-spec (:body a*)))]
    (assoc-in a (conj path ::ret-spec) body-ret-spec)))

(defmethod infer* :letfn [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (-> a* :body ::ret-spec))))

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
