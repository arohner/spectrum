(ns spectrum.flow
  (:require [clojure.core.memoize :as memo]
            [clojure.core.match :refer [match]]
            [clojure.data :refer [diff]]
            [clojure.java.io :as io]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.tools.reader :as reader]
            [clojure.tools.reader.reader-types :as readers]
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
(declare infer-walk)

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
(def flow (memo/memo (fn
                       ([a]
                        {:post [%]}
                        (flow* a []))
                       ([a path]
                        {:post [%]}
                        (flow* a path)))))

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
    (= :def (:op a)) (println "infer-result:" (-> a :var) "=>" (-> a :init maybe-strip-meta ::ret-spec))))

(def cached-infer (memo/memo (fn [a path]
                               {:post [(when a
                                         %)]}
                               (let [a* (infer* a path)]
                                 (infer-result (get-in a* path))
                                 a*))))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis) :ret ::analysis)
(defn infer
  "Given an un-spec'd analysis, return our best guess for the spec"
  ([a]
   (infer a []))
  ([a path]
   (cached-infer a path)))

(defn flow-ns
  "Given the result of analyze-ns, flow all forms"
  [as]
  (mapv flow as))

(defn assoc-in-a [a path data]
  (if (seq path)
    (do
      (when-let [op (:op (get-in a path))]
        (assert (= op (:op data))))
      (assoc-in a path data))
    data))

(s/fdef maybe-assoc-var-name :args (s/cat :a ::analysis) :ret ::analysis)
(defn maybe-assoc-var-name
  "Given a def analysis, if the def stores a fn, update the :fn analysis to contain the varname, for future analysis"
  [a]
  (let [path (if (-> a :init :op (= :with-meta))
               [:init :expr]
               [:init])]
    (if (= :fn (:op (get-in a path)))
      (assoc-in-a a (conj path ::var) (:var a))
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

(defn var-macro?
  "True if this var holds a macro"
  [v]
  (-> v meta :macro))

(s/fdef macro-var :args (s/cat :a ::ana.jvm/analysis) :ret (s/nilable var?))
(defn macroexpansion-var
  "If the analysis node is a macroexpansion, return the macro's var or nil"
  [a]
  {:post [(or (nil? %) (var? %))]}
  (->> a
       :raw-forms
       (map (fn [f]
              (-> f  meta :clojure.tools.analyzer/resolved-op)))
       (filter var-macro?)
       first))

(defn patch-doseq [a]
  ;;; doseq contains an expression

  ;; (loop [chunk nil
  ;;        count 0
  ;;        i 0]
  ;;   (if (< i count)
  ;;     (.nth chunk i)
  ;;     ...))

  ;; this .nth call is unreachable in the first iteration, but is
  ;; always IChunk when (< i count) is true. (.nth nil) fails the type
  ;; checker, but never happens, so convince spectrum its type is
  ;; IChunk

  (if (some-> a macroexpansion-var (= #'doseq))
    (-> a
        (update-in [:bindings 1] (fn [b]
                                   (assert (-> b :name name (#(re-find #"^chunk" %))))
                                   (-> b
                                       (assoc ::ret-spec (c/class-spec clojure.lang.IChunk)
                                              :skip? true)))))
    a))

(defn wrap [f]
  (fn [a path]
    (let [a* (get-in a path)]
      (try
        (binding [*a* a*]
          (let [a (update-in a path patch-doseq)
                a* (get-in a path)
                _ (assert a*)
                a (if-not (::skip? a*)
                    (f a path)
                    a)
                a* (get-in a path)]
            (when-not (s/valid? ::c/spect-like (::ret-spec a*))
              (println "walk failed:" f (:form a*) (:op a*) "=>" (::ret-spec a*))
              (println (s/explain-str ::c/spect-like (::ret-spec a*))))
            (validate! ::c/spect-like (::ret-spec a*))
            a))
        (catch Throwable t
          (println "walk" f " exception while walking:" (.getMessage t) (a-loc-str a*) (:op a*) (:form a*))
          (throw t))))))

(def flow-wrap (wrap flow*))

(s/fdef walk-a :args (s/cat :f fn? :a ::ana.jvm/analysis :path vector?) :ret ::analysis)
(defn walk-a
  "Given an analysis a, recursively call f on all of a's children"
  [f a path]
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
  (walk-a flow-wrap a path))

(defn analyze-cache-dispatch [a path]
  (-> a (get-in path) :op))

(defmulti analyze-cache* #'analyze-cache-dispatch)

(defn analyze-cache-walk [a path]
  (walk-a analyze-cache* a path))

(defmethod analyze-cache* :default [a path]
  (analyze-cache-walk a path)
  a)

(defmethod analyze-cache* :def [a path]
  (let [a* (get-in a path)
        v (:var a*)]
    (assert (var? v))
    (data/store-var-analysis v a)
    (analyze-cache-walk a path)
    a))

(defn analyze-cache [a]
  (analyze-cache* a []))

(defn analyze-cache-ns
  "analyze and store in var cache, but don't flow or check"
  [ns]
  (println "analyzing" ns)
  (let [as (ana.jvm/analyze-ns ns)]
    (doseq [a as]
      (analyze-cache a))
    (data/mark-ns-analyzed! ns)))

(defmethod flow* :default [a path]
  (assert false (format "unhandled: %s %s" (:op (get-in a path)) (a-loc-str (get-in a path)))))

(defmethod flow* :quote [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in-a a (conj path ::ret-spec) (-> a* :expr ::ret-spec))))

(defmethod flow* :binding [a path]
  a)

(s/fdef recursive? :args (s/cat :a ::ana.jvm/analysis :path ::path) :ret boolean?)
(defn recursive?
  "Given an invoke of var v at a path, return true if it's a self-call"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :var (:op a*)))
        v (:var a*)]
    (assert (var? v))
    (loop [path path]
      (let [a* (get-in a path)]
        (if (and (= :def (:op a*)) (= v (:var a*)))
          true
          (if (seq path)
            (recur (pop path))
            false))))))

(s/fdef get-self-call-analysis :args (s/cat :a ::ana.jvm/analysis :path ::path) :ret (s/nilable ::ana.jvm/analysis))
(defn get-self-call-analysis
  "Given a self-call of var v, return the :fn analysis"
  [a path]
  {:post [%]}
  (let [a* (get-in a path)
        _ (assert (= :var (:op a*)))
        v (:var a*)]
    (assert (recursive? a path))
    (loop [path path]
      (let [a* (get-in a path)]
        (if (and (= :fn (:op a*)) (or (= v (:var (get-in a (pop path))))
                                      (= v (:var (get-in a (pop (pop path)))))))
          a*
          (if (seq path)
            (recur (pop path))
            nil))))))

(defn get-var-spec
  "Get or infer the spec for v, appearing at [a path]"
  [v a path]
  {:post [(c/spect? %)]}
  (let [a* (get-in a path)]
    (or (c/get-var-spec v)
        (data/get-var-spec v)
        (if-let [v-a (data/get-var-analysis v)]
          (if (recursive? a path)
            (::ret-spec (get-self-call-analysis a path))
            (::ret-spec (infer v-a [])))
          (c/unknown {:message (format "couldn't find spec or analysis for %s at %s" v (a-loc-str (get-in a path)))})))))

(defmethod flow* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        a* (get-in a path)
        v (:var a*)
        _ (assert (var? v))
        _ (data/store-var-analysis v a)
        a (flow-walk a path)
        _ (data/store-var-analysis v a)]
    (assoc-in a (conj path ::ret-spec) (c/pred-spec #'var?))))

(defmethod flow* :the-var [a path]
  ;; the-var => (var foo). Returns the actual var
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in-a a (conj path ::ret-spec) (c/value (:var a*)))))

(defmethod flow* :var [a path]
  ;; :var => the value the var holds
  (let [a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (get-var-spec v a path)]
    (assoc-in-a a (conj path ::ret-spec) ret-spec)))

(defmethod flow* :with-meta [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in-a a (conj path ::ret-spec) (::ret-spec (:expr a*)))))

(s/fdef invoke-get-fn-spec :args (s/cat :a ::analysis :p ::path :args c/spect?) :ret (s/nilable ::c/spect))

(defn invoke-get-fn-spec-dispatch [a path _]
  (-> (get-in a path) :op))

(defmulti invoke-get-fn-spec "Given the :fn from an :invoke a, return the spec for the thing being invoked"
  #'invoke-get-fn-spec-dispatch)

(defmethod invoke-get-fn-spec :var [a path _]
  {:post [(or (nil? %) (c/spect? %) (do (when-not (c/fn-spec? %)
                                          (println "invoke-get-fn-spec:" (-> (get-in a path) :var) "=>" %))
                                        true))]}
  (let [a* (get-in a path)
        v (-> a* :var)]
    (assert (var? v))
    (or (data/get-var-spec v)
        (when (recursive? a path)
          (::ret-spec (get-self-call-analysis a path)))
        (when-let [v-a (data/get-var-analysis v)]
          (-> v-a infer :init maybe-strip-meta ::ret-spec))
        (do
          (println "warning: couldn't find spec or analysis for" v)
          (c/unknown {:message (format "couldn't find spec or analysis for %s" v)})))))

(defn find-binding-fn-definition
  "find-binding, when name is a :fn, unwrap until we find the definition"
  [a path name]
  (loop [path path]
    (let [ret (find-binding a path name)]
      (if (= :fn (:op ret))
        ret
        (if (and (= :local (:op ret)) (seq path))
          (do
            (recur (pop path)))
          nil)))))

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

(defmethod invoke-get-fn-spec :local [a path args]
  {:post [(c/spect? %)]}
  (let [a* (get-in a path)
        b (find-binding a (pop path) (:name a*))
        ret (::ret-spec b)]
    ret))

(defmethod invoke-get-fn-spec :fn [a path _]
  (let [a (infer a path)
        ret-spec (::ret-spec (get-in a path))]
    (assert ret-spec)
    ret-spec))

(defmethod invoke-get-fn-spec :default [a path _]
  (let [a* (get-in a path)]
    (c/unknown {:message (format "don't know how to get spec or analysis for %s %s" (:op a*) (:form a*))})))

(defmethod flow* :fn [a path]
  (let [;;a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (invoke-get-fn-spec a path (:args a*))
        a (assoc-in-a a (conj path ::ret-spec) ret-spec)
        a (if (:inferred ret-spec)
            a
            (flow-walk a path))]
    a))

(defn find-binding*-dispatch [a name]
  {:pre [(:op a) (symbol? name)]}
  (when-not name
    (println "find-binding dispatch no name for" (:op a)))
  (:op a))

(s/def :binding/name symbol?)
(s/def :binding/path vector?)
(s/def :binding/spect c/spect?)

(s/def ::binding (s/keys :req-un [:binding/name :binding/path :binding/spect]))

(defmulti find-binding* #'find-binding*-dispatch)

(defn find-binding-key [key]
  (fn find-binding [a name]
    (some->> (get a key)
             (map-indexed (fn [i b]
                            (assoc b :index i)))
             (filter (fn [b]
                       (= name (:name b))))
             first
             (#(assoc % :path [key (:index %)])))))

(def find-binding-let (find-binding-key :bindings))
(def find-binding-if (find-binding-key :if-bindings))

(defn find-binding-default [a name]
  (or (find-binding-if a name)
      (find-binding-let a name)))

(defmethod find-binding* :default [a name]
  (find-binding-default a name))

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
    a))

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

(defn find-binding- [a path name]
  (loop [path* path]
    (assert (vector? path))
    (let [a* (get-in a path*)
          b (when (:op a*)
              (find-binding* a* name))]
      (if b
        (assoc b :path (into path* (:path b)))
        (when (seq path*)
          (let [p* (pop path*)]
            (recur p*)))))))

(defn if-test
  "Given an :if, return the test.

Tries harder to find the 'logical' test, if the code does, e.g.

(let [y (instance? C x)]
  (if y
   ...
   ...))

will return `(instance? C x)` rather than `y`
"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :if (:op a*)))
        {:keys [test]} a*]
    (if (= :local (:op test))
      (let [b (find-binding- a path (:name test))]
        (if (:init b)
          (:init b)
          test))
      test)))

(defn if-test-type
  "Given an :if, return a keyword representing the type of test it is doing, or :unknown"
  [a path]
  {:post [(keyword? %)]}
  (let [a* (get-in a path)
        _ (assert (= :if (:op a*)))
        {:keys [test then else]} a*
        test (if-test a path)]
    (cond
      (invoke-predicate? test) :pred
      (invoke-nil? test) :nil
      (invoke-truthy? test) :truthy
      (= :instance? (:op test)) :instance?
      :else :unknown)))

(defn if-test-binding
  "Given an :if, return the path to the local binding it tests, or nil
  if unknown, or not testing a local variable"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :if (:op a*)))
        {:keys [test then else]} a*
        test (if-test a path)
        binding-name (case (if-test-type a path)
                       (:pred :nil) (-> test :args first :name)
                       :truthy (-> test :name)
                       :instance? (-> test :target :name)
                       :unknown nil)]
    (when binding-name
      (-> (find-binding a path binding-name)
          :path))))

(defn binding-update-if-specs
  "Given a :binding, walk up the analysis update the binding's ::ret-spec to reflect
  `if` branches taken. Returns the updated binding"
  [a path binding]
  {:pre [(map? binding)]}
  (loop [path path
         spec (::ret-spec binding)]
    (let [a* (get-in a path)]
      (assert spec (format "no ::ret-spec on %s" (:form binding) "in" (:form a*)))
      (if (and a* (seq path))
        (let [parent (get-in a (pop path))]
          (if (= :if (:op parent))
            (let [{:keys [test then else]} parent
                  test (if-test a (pop path))
                  this-expr (cond
                              (and (= (:form a*) (:form test)) (= (a-loc a*) (a-loc test))) :test
                              (and (= (:form a*) (:form then)) (= (a-loc a*) (a-loc then))) :then
                              (and (= (:form a*) (:form else)) (= (a-loc a*) (a-loc else))) :else
                              :else (do
                                      (assert false)))
                  test-type (if-test-type a (pop path))]
              (if (and (not= :unknown test-type)
                       (or (-> test :form (= (:form binding)))
                           (-> test :args first :name (= (:name binding)))
                           (-> test :target :name (= (:name binding)))))
                (let [test-pred (condp = test-type
                                  :nil  (c/pred-spec #'nil?)
                                  :pred (c/pred-spec (-> test :fn :var))
                                  :truthy (c/pred-spec #'identity)
                                  :instance? (c/class-spec (:class test)))
                      _ (assert test-pred)
                      updated-spec-then (condp = test-type
                                          :pred (c/and- [spec test-pred])
                                          :nil (c/value nil)
                                          :truthy (-> spec (c/and-not (c/pred-spec #'nil?)) (c/and-not (c/pred-spec #'false?)))
                                          :instance? (c/and- [spec (c/class-spec (:class test))]))
                      updated-spec-else  (condp = test-type
                                           :pred (c/and-not spec test-pred)
                                           :nil (c/and-not spec test-pred)
                                           :truthy (c/or- [(c/value nil) (c/value false)])
                                           :instance? (c/and-not spec test-pred))]
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
  {:pre [(symbol? name)]
   :post [(s/valid? (s/nilable ::analysis) %)]}
  (when-let [b (find-binding- a path name)]
    (binding-update-if-specs a path b)))

(defn apply-constraints [a constraints]
  (reduce (fn [a [b-path spec]]
            (update-in a (conj b-path ::ret-spec) c/add-constraint spec)) a constraints))

(defn maybe-if-bindings
  "Given a path, walk upwards to the nearest :if-binding, or nil"
  [a path]
  (loop [path path]
    (if (-> (get-in a path) :if-bindings)
      (conj path :if-bindings)
      (if (not= [] path)
        (recur (pop path))
        nil))))

(s/fdef infer-add-constraint :args (s/cat :a ::analysis :b-path vector? :call-path vector? :constraint c/spect?))
(defn infer-add-constraint
  "Given an operation at call-path, update binding at b-path to add a constraint on method-spec."
  [a b-path call-path constraint]
  {:pre [(vector? b-path)]
   :post [(map? %)]}
  (let [binding (get-in a b-path)
        _ (assert binding)
        if-bindings (maybe-if-bindings a call-path)
        b-spec (::ret-spec binding)]
    (assert binding (format "binding not found: %s %s" (:form a) b-path))
    (assert b-path)
    (if if-bindings
      (if (= :if-bindings (last b-path))
        (assert false "TODO: update an if-binding")
        (let [binding (update-in binding [::ret-spec] c/add-constraint constraint)
              binding (merge binding {:call-path call-path
                                      :path b-path
                                      :constraint constraint})]
          (update-in a if-bindings conj binding)))
      (update-in a (conj b-path ::ret-spec) c/add-constraint constraint))))

(s/fdef analysis-args->spec :args (s/cat :a ::ana.jvm/analyses) :ret ::c/spect)
(defn analysis-args->spec
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/cat- (mapv (fn [arg]
                  (when-not (::ret-spec arg)
                    (println "no ret-spec:" (:form arg) (:op arg)))
                  (assert (::ret-spec arg))
                  (c/maybe-spec-spec (::ret-spec arg))) args)))

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

(defn invoke-get-fn-analysis-var [v]
  (let [v-a (data/get-var-analysis v)
        path [:init]
        path (if (-> (get-in v-a path) :op (= :with-meta))
               (conj path :expr)
               path)]
    (when v-a
      {:a v-a :path path :op :var})))

(defn invoke-get-fn-analysis [a path]
  (let [a* (get-in a path)
        _ (assert (= :invoke (:op a*)) (format "invoke-get-fn-analysis passed %s %s" (:op a*) (:form a*)))
        f (:fn a*)
        fn-op (-> a* :fn :op)]
    (condp = fn-op
      :var (invoke-get-fn-analysis-var (-> a* :fn :var))
      :the-var (invoke-get-fn-analysis-var (-> a* :fn :var))
      :fn  {:a (-> a* :fn) :path (conj path :fn) :op fn-op}
      :local (let [b (find-binding a path (-> a* :fn :name))]
               (assert b)
               (assert (:path b))
               {:a (:init b)
                :path (:path b)
                :op fn-op})
      :const {:a (-> a* :fn :val)
              :path (conj path :fn)
              :op fn-op}
      :invoke (recur a (conj path :fn))
      (println "don't know how to find analysis for" fn-op))))

(defn contains-control-flow? [s]
  {:pre [(c/spect? s)]}
  (some c/control-flow? (c/elements s)))

(s/fdef strip-control-flow :args (s/cat :s (s/nilable c/spect?)) :ret (s/nilable c/spect?))
(defn strip-control-flow
  "Given the ret-spec for a function, remove control flow (recur and throw) from the type."
  [s]
  {:pre [(c/spect? s)]
   :post [(c/spect? %)]}
  (cond
    (not (contains-control-flow? s)) s
    (c/control-flow? s) (c/bottom {:message "only control flow"})
    (c/or? s) (c/or- (remove c/control-flow? (c/elements s)))
    :else (assert false (format "Don't know how to strip control flow from %s" (print-str s)))))

(def control-flow-ops #{:case :fn-method :if :letfn :method :quote})

(defn top-level-expression?
  "True if this expression is guaranteed to be invoked when the file is loaded, i.e. no control flow blocking it"
  [a path]
  (if (nil? (seq path))
    true
    (let [a* (get-in a path)]
      (if (not (contains? control-flow-ops (:op a*)))
        (recur a (pop path))
        false))))

(defn top-level-load?
  "True if this expression invokes clojure.core/load from the top level"
  [a path]
  (let [a* (get-in a path)]
    (and
     (-> a* :op (= :invoke))
     (-> a* :fn :var (= #'load))
     (top-level-expression? a path))))

(defn analyze-load
  "when encountering a call to `clojure.core/load` for `path` during analyze-ns, analyze the file. `ns` is the ns currently being analyzed"
  [ns env ^String path]
  (let [filename (if (.startsWith path "/")
                   path
                   (str (#'clojure.core/root-directory (ns-name ns)) \/ path))]
    (println "analyze-load:" filename)
    (with-open [rdr (io/reader path)]
      (let [pbr (readers/indexing-push-back-reader
                 (java.io.PushbackReader. rdr) 1 filename)
            eof (Object.)
            read-opts {:eof eof :features #{:clj :t.a.jvm}}
            read-opts (if (.endsWith filename "cljc")
                        (assoc read-opts :read-cond :allow)
                        read-opts)]
        (loop []
          (let [form (reader/read read-opts pbr)
                env (assoc env :ns (ns-name ns))]
            (when-not (identical? form eof)
              (swap! clojure.tools.analyzer.env/*env* update-in [::analyzed-clj path]
                     (fnil conj [])
                     (clojure.tools.analyzer.jvm/analyze form env))
              (recur))))))))

(defn infer-or-flow
  "Given analysis flow or infer as appropriate. Return the updated analysis"
  [a path]
  {:post [(= (:op %) (:op a))
          (if a
            (get-in % (conj path ::ret-spec))
            true)]}
  (if (::ret-spec a)
    a
    (if-let [v (:var a)]
      (if-let [s (c/get-var-spec v)]
        (flow a path)
        (infer a path))
      (infer a path))))

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

(s/fdef macro? :args (s/cat :a ::ana.jvm/analysis) :ret boolean?)
(defn macro?
  "True if this analysis is in a macro definition (top level of the form is :def, and the var is a macro)"
  [a]
  (match a
    {:op :do :statements ([{:op :def :var (_ :guard #(-> % meta :macro))} & rest] :seq)} true
    :else false))

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
                 s (c/will-accept spec)]
             (assert (c/spect? s))
             (if (:variadic? param)
               (conj ret (assoc param ::ret-spec spec))
               (recur (conj ret (assoc param ::ret-spec s)) (rest params) (c/rest- spec))))
           ret))
       (mapv (fn [p]
               (assoc p ::ret-spec (c/invalid {:form (:name p) :message "destructure failed"}))) params-original))))
  ([params spec]
   (destructure-fn-params params spec false)))

(s/fdef call-site-specialize :args (s/cat :f-a ::analysis :args c/spect?) :ret c/spect?)
(defn call-site-specialize*
  "Given the analysis for a fn and fn args, return a call-site specialized spec for f. specialization can change the :args, e.g. `map`, so this returns a whole fn spec"
  [f-a path args-spec]
  {:pre [(c/spect? args-spec)]
   :post [(c/fn-spec? %)]}
  (let [f-a* (get-in f-a path)
        f-spec (::ret-spec f-a*)
        unspecialized-ret-spec (or (:ret f-spec) (c/unknown {:message (format "call-site-specialize: no ret-spec on %s" (print-str f-spec))} ))
        _ (assert (c/invoke? f-spec))
        v (:var f-a*)]

    ;; there are invokable things we can't specialize, such as IFn, multimethods, etc.
    (if (= :fn (:op f-a*))
      (if (and v (data/get-invoke-transformer v))
        (let [s (get-var-spec v f-a path)]
          (c/invoke s args-spec))
        (if (c/valid? (c/invoke-accept f-spec) args-spec)
          (let [_ (when-not (c/conformy? args-spec)
                    (println "call-site-specialize:" (:form f-a) args-spec))
                _ (assert (c/conformy? args-spec))
                _ (when-not (= :fn (:op f-a*))
                    (println "specialize:" f-a path (:op f-a*)))
                _ (assert path)
                f-a (infer-or-flow f-a path)
                f-a* (get-in f-a path)
                _ (assert (::ret-spec f-a*))
                specialized-methods (->> (get-in f-a* [:methods])
                                         (filterv (fn [m]
                                                    (assert (::ret-spec m))
                                                    (assert (c/fn-spec? (::ret-spec m)))
                                                    (when-not (c/valid? (-> m ::ret-spec :args) args-spec)
                                                      (println "specialize method" (:form f-a*) (-> m ::ret-spec) args-spec "=>" (c/conform (-> m ::ret-spec :args) args-spec) ))
                                                    (c/valid? (-> m ::ret-spec :args) args-spec))))

                _ (when-not (= 1 (count specialized-methods))
                    (println "specialize method count:" (:form f-a) (map ::ret-spec (:methods f-a*)) "args" args-spec "=>" (count specialized-methods) specialized-methods))
                _ (assert (= 1 (count specialized-methods)))
                f-a* (assoc-in-a f-a* [:methods] specialized-methods)
                f-a (assoc-in-a f-a path f-a*)
                f-a (update-in f-a (conj path [:methods 0 :params]) (fn [params]
                                                                      (destructure-fn-params params args-spec)))
                orig-spec (::ret-spec f-a)
                f-a (flow* f-a path)
                f-spec* (get-in f-a (conj path ::ret-spec))]
            (println "specialize:" (or (:var f-a) (:form f-a)) args-spec "=>" f-spec*)
            (assert (c/spect? f-spec*))
            f-spec*)
          f-spec))
      f-spec)))

(def call-site-specialize (memo/memo call-site-specialize*))

(defmethod flow* :invoke [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        fn-spec (-> a* :fn ::ret-spec)
        args-spec (analysis-args->spec (:args a*))
        arg-count (count (:args a*))
        {f-a :a f-a-path :path} (invoke-get-fn-analysis a path)
        fn-spec (if fn-spec
                  fn-spec
                  (when f-a
                    (assert false)))]
    (try
      (assert (c/spect? fn-spec))
      (assert (c/spect? args-spec))
      (when (-> a* :fn :var (= #'load))
        (println "load"))
      (when (top-level-load? a path)
        (println "toplevel load" (-> a* :args) "@" (a-loc-str a)))
      (if (or (and f-a (= :fn (:op f-a)) (invoke-valid-arity? f-a arg-count))
              (not f-a)
              (not= :fn (:op f-a)))
        (if fn-spec
          (let [a (assoc-in-a a (conj path ::fn-spec) fn-spec)]
            (assert (c/spect? fn-spec))
            (assert (c/spect? args-spec))
            (assoc-in-a a (conj path ::ret-spec) ;; if f-a
                      ;; (:ret (call-site-specialize f-a f-a-path args-spec))
                        (c/invoke fn-spec args-spec)))
          (assoc-in-a a (conj path ::ret-spec) (c/unknown {:message (format "invoke: no spec for %s" (:var (:fn a*)))})))
        (assoc-in-a a (conj path ::ret-spec) (c/invalid {:message (format "invoke: wrong number of args %s" (:form a*))})))
      (catch Exception e
        (println e "flow :invoke while walking:" (:form a*) (a-loc-str a))
        (throw e)))))

(defmethod flow* :protocol-invoke [a path]
  (let [a* (get-in a path)
        v (-> a* :fn :var)
        spec (when v
               (get-var-spec v a path))
        a (flow-walk a path)
        a* (get-in a path)
        args-spec (analysis-args->spec (:args a*))]
    (assoc-in-a a (conj path ::ret-spec) (if spec
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
    (when-not (c/spect? then-ret-spec)
      (println "walk-if then not spect:" (:form (:then a*)) (-> a* :then ::ret-spec) (-> a* :then :op)))
    (when-not (c/spect? else-ret-spec)
      (println "walk-if else not spect:" (:form (:else a*)) (-> a* :else ::ret-spec) (-> a* :else :op)))
    (assoc-in-a a (conj path ::ret-spec) (condp = truthyness
                                           :truthy then-ret-spec
                                           :falsey else-ret-spec
                                           :ambiguous (c/or- [then-ret-spec
                                                              else-ret-spec])))))
(defmethod flow* :if [a path]
  (walk-if flow-walk a path))

(defmethod flow* :const [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (assoc-in-a a (conj path ::ret-spec) (c/value (:val a*)))))

(defmethod flow* :do [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        ret-spec (or (some c/throw? (:statements a*)) (-> a* :ret ::ret-spec))]
    (assoc-in-a a (conj path ::ret-spec) ret-spec)))

(defn walk-catch [walk-fn a path]
  {:post [(s/valid? ::analysis (get-in % path))]}
  (let [a (walk-fn a path)
        a* (get-in a path)]
    (assert (or (map? (:body a*)) (nil? (:body a*))))
    (assoc-in-a a (conj path ::ret-spec) (if (:body a*)
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
    (assoc-in-a a (conj path ::ret-spec) (c/or- (map ::ret-spec (concat body catches))))))

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
    (assoc-in-a a (conj path ::ret-spec) ret-spec)))

(defn resolve-java-class-spec [x]
  (c/class-spec (j/resolve-java-class x)))

(defn class-is-deftype? [cls]
  (isa? cls clojure.lang.IType))

(defn class-is-defrecord? [cls]
  (isa? cls clojure.lang.IRecord))

(s/fdef defrecord-create? :args (s/cat :cls class? :method symbol?) :ret boolean?)
(defn defrecord-create? [cls method]
  (and (or (class-is-deftype? cls) (class-is-defrecord? cls))
       (= method 'create)))

(defn method-type->spec [method-type]
  (let [c (j/resolve-java-class method-type)]
    (if (j/primitive? c)
      (c/class-spec c)
      (c/or- [(c/class-spec c) (c/pred-spec #'nil?)]))))

(s/fdef compatible-java-method-relaxed? :args (s/cat :arg-spec ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
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
  "Return all arities"
  [cls method]
  (some->> (reflect/reflect cls)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Method m)
                           (= method (:name m)))))))

(defn method->spec [m]
  (let [declaring-class (j/resolve-java-class (:declaring-class m))]
    (or
     (data/get-updated-method-spec declaring-class
                                   (:name m)
                                   (mapv j/resolve-java-class (:parameter-types m)))
     (c/fn-spec (c/cat- (concat (if (:static (:flags m))
                                  [(c/value declaring-class)]
                                  [(c/class-spec declaring-class)])
                                (mapv (fn [param]
                                        (method-type->spec param)) (:parameter-types m))))
                (method-type->spec (j/resolve-java-class (:return-type m)))
                nil))))

(defn get-java-method-spec
  "Returns the spec for all arities of the method or'd together.

  Spec will include the an instance of the class as the first arg, or the class itself for static methods."
  [cls method]
  (->> (get-java-method cls method)
       (map method->spec)
       (c/merge-fn-specs)))

(s/fdef get-compatible-java-methods :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret (s/nilable (s/coll-of j/reflect-method?)))
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

(s/fdef java-spec-with-nil :args (s/cat :x c/class-spec?) :ret c/spect?)
(defn java-spec-with-nil
  "Java functions are all implicitly (or nil), unless primitive."
  [s]
  (let [c (:cls s)]
    (assert (class? c))
    (if (j/primitive? c)
      s
      (c/or- [s (c/value nil)]))))

(defn multimethod? [x]
  (instance? clojure.lang.MultiFn x))

(defn defmethod? [a]
  (let [{:keys [class method instance]} a
        v (:var instance)]
    (and (= :instance-call (:op a)) (= method 'addMethod) (some-> v deref multimethod?))))

(s/fdef maybe-flow-multi-method :args (s/cat :a ::analysis) :ret ::analysis)
(defn maybe-flow-multi-method [a path]
  (let [{:keys [class method instance]} a
        v (:var instance)
        a* (get-in a path)]
    (if (defmethod? a*)
      (let [[dispatch-val f] (:args a*)
            a (assoc-in-a a (concat path [:args 1 ::var]) v)
            a* (get-in a path)]
        (data/store-defmethod-analysis a*)
        a)
      a)))

(defn flow-java-call
  "Handles both :static-call and :instance-call"
  [a path]
  (let [a (maybe-flow-multi-method a path)
        a* (get-in a path)
        {:keys [class method instance]} a*]
    (if (and class method)
      (let [cls-or-inst (if (:instance a*)
                          (-> a* :instance ::ret-spec)
                          (-> a* :class c/value))
            _ (validate! ::c/spect cls-or-inst)
            invoke-args (c/cat- (concat
                                 [cls-or-inst]
                                 (mapv (fn [arg] (::ret-spec arg)) (:args a*))))
            spec (get-java-method-spec class method)
            meth (get-conforming-java-method class method invoke-args)
            method-spec (if (and meth spec (c/known? (:args spec)))
                   (c/maybe-transform-method meth spec invoke-args)
                   spec)
            ret-spec (if (c/fn-spec? spec)
                       (do
                         (assert (:ret spec))
                         (if (c/every-known? invoke-args)
                           (:ret spec)
                           (c/unknown {:form (:form a*) :message (format "invoke %s with unknown args %s" (print-str spec) (print-str invoke-args))}))(:ret spec))
                       (do
                         (assert (c/invalid? spec))))]
        (assert ret-spec)
        (assoc-in-a a (conj path ::ret-spec) ret-spec))
      (do
        (println "flow java no spec on reflection:" (:form a*) class method)
        (assert false)
        (assoc-in-a a (conj path ::ret-spec) (c/unknown {:message (format "no spec on reflection: %s" (:form a))}))))))

(defmethod flow* :static-call [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)]
    (flow-java-call a path)))

(defmethod flow* :instance-call [a path]
  (let [a (flow-walk a path)
        a (flow-java-call a path)]
    a))

(defmethod flow* :local [a path]
  (let [a (flow-walk a path)
        a* (get-in a path)
        b (find-binding a (pop path) (:name a*))]
    (assert b (format "flow :local: failed to find binding: %s %s %s" (:name a*) (:form a*) (a-loc-str a*)))
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
  (let [a (flow-loop-let a path)
        a* (get-in a path)]
    (update-in a (conj path ::ret-spec) (fn [s]
                                          {:pre [(c/spect? s)]}
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
                                                                       (update-in b [::ret-spec] (fn [existing]
                                                                                                   (c/or- [existing s])))) bindings loop-specs*)))]
            (walk-fn (assoc-in a (conj path ::walked?) true) loop-path))))
      (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "recur bad arity, loop takes %s args, got %s" loop-arg-count recur-arg-count)})))))

(defmethod flow* :recur [a path]
  (walk-recur flow-walk a path))

(s/fdef flow-method* :args (s/cat :a ::analysis :path vector? :args (s/nilable c/spect?)))
(defn flow-method* [a path args-spec]
  (assert args-spec (format "flow-method: no spec for %s" (:form (get-in a (pop (pop path))))))
  (let [a* (get-in a path)
        a (update-in a (conj path :params) destructure-fn-params args-spec (macro? a))
        a (flow* a (conj path :body))]
    a))

(defn flow-method [a path]
  (let [a* (get-in a path)
        fn-a* (get-in a (pop (pop path)))
        _ (assert (= :fn (:op fn-a*)))
        s (invoke-get-fn-spec a (pop (pop path)) nil)
        a (assoc-in a (conj path ::ret-spec) s)
        a (if (:args s)
            (flow-method* a path (:args s))
            a)]
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
  (assert (c/cat? java-args-spec))
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
        java-spec (get-conforming-java-method interface method (analysis-args->spec params))
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
    (assoc-in a (conj path ::ret-spec) (c/throw-form (c/class-spec (-> a* :exception :class :val))))))

(s/fdef keyword-invoke-ret-spec :args (s/cat :a ::analysis) :ret c/spect?)
(defn keyword-invoke-ret-spec
  [a]
  (let [spec (-> a :target ::ret-spec)
        k (-> a :keyword :val)]
    (assert k)
    (assert spec)
    (if (c/keyword-invoke? spec)
      (c/keyword-invoke spec (c/cat- [k]))
      (c/pred-spec #'any?))))

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

(def infer-wrap (wrap infer))

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

(defmethod infer* :def [a path]
  (let [a* (get-in a path)
        a (assoc-in-a a path (maybe-assoc-var-name a*))
        v (:var a*)
        _ (data/store-var-analysis v a)
        a (infer-walk a path)
        a* (get-in a path)]
    (data/store-var-analysis v a)
    (when (-> a* :init)
      (let [s (-> a* :init ::ret-spec)]
        (assert (c/spect? s))
        (data/store-var-spec v s)))
    (assoc-in a (conj path ::ret-spec) (c/pred-spec #'var?))))

(defmethod infer* :var [a path]
  ;; :var => the value the var holds
  (let [a (flow-walk a path)
        a* (get-in a path)
        v (:var a*)
        ret-spec (get-var-spec v a path)]
    (assert (c/spect? ret-spec))
    (assoc-in a (conj path ::ret-spec) ret-spec)))

(defmethod infer* :the-var [a path]
  ;; the-var => (var foo). Returns the actual var
  (let [a (infer-walk a path)
        a* (get-in a path)]
    (assoc-in a (conj path ::ret-spec) (c/value (:var a*)))))

(defn update-fn [s f & args])

(s/fdef infer-fn-invoke-add-constraint)
(defn infer-fn-invoke-add-constraint
  "Given an invoke to the fn at binding b with args, update b's spec to support the call"
  [a b-path call-path invoke-args]
  (let [b (get-in a b-path)
        s (::ret-spec b)]
    (assert b)
    (assert s)
    (infer-add-constraint a b-path call-path (c/fn-spec invoke-args (c/pred-spec #'any?) nil))))

(s/fdef infer-invoke-constraints :args (s/cat :s c/spect? :args (s/coll-of c/spect?) :ret c/spect?))
(defn infer-invoke-constraints
  "Given a spec (which could accept multiple type or arities), and a
  seq of partially constrained argument specs, constrain all
  arguments, returning a spec representing all possible concrete specs
  that args could conform to"
  [spec args]
  {:pre [(validate! c/spect? spec)
         (s/assert c/conformy? spec)
         (not (c/spect? args))
         (not (c/fn-spec? spec))
         (validate! (s/coll-of c/spect?) args)]
   :post [(validate! c/spect? %)]}
  (if (not (c/unknown? spec))
    (let [rets (->> (c/all-possible-values spec (count args))
                    (filter (fn [s]
                              (<= (c/min-length s) (count args))))
                    (filter (fn [s]
                              (every? (fn [[s a]]
                                        (c/non-contradiction? a s)) (map vector (c/elements s) args)))))]
      (if (seq rets)
        (c/or- rets)
        (do
          (println "infer-invoke invalid:" spec args)
          (c/invalid {:message (format "infer-invoke-constraints: can't invoke %s with %s" (print-str spec) (print-str args))}))))
    spec))

(defmethod infer* :invoke [a path]
  {:post [(::ret-spec (get-in % path))]}
  (let [a-orig a
        a* (get-in a path)
        a (infer-walk a path [:args])
        a* (get-in a path)
        invoke-args (c/cat- (mapv (fn [arg] (::ret-spec arg)) (:args a*)))
        _ (when (not (c/conformy? invoke-args))
            (println "invoke: bad args" (:form a*) (mapv (fn [arg] (::ret-spec arg)) (:args a*))))
        _ (assert (every? c/conformy? (:ps invoke-args)))
        invoke-var? (boolean (get-in a (concat path [:fn :var])))
        local-inferred-fn? (and (contains? #{:binding :local} (-> a* :fn :op)))
        a (if local-inferred-fn?
            (let [fn-name (-> a* :fn :name)
                  _ (assert (-> a* :fn :name))
                  b (find-binding a path (-> a* :fn :name))]
              (assert b)
              (-> a
                  (infer-add-constraint (:path b) path (c/pred-spec #'ifn?))
                  (infer-fn-invoke-add-constraint (:path b) path invoke-args)))
            a)
        s (invoke-get-fn-spec a (conj path :fn) invoke-args)
        {f-a :a f-a-path :path f-a-op :op} (invoke-get-fn-analysis a path)]
    (if (and s (not (c/unknown? s)) (not (c/invalid? s)) (or (c/invoke? s) local-inferred-fn?))
      (let [s-args (if (c/valid? (c/invoke-accept s) invoke-args)
                     (let [spec* (c/maybe-transform s invoke-args)]
                       (if (:args spec*)
                         (:args spec*)
                         (c/invoke-accept s)))
                     (c/invoke-accept s))
            s-args (infer-invoke-constraints s-args (c/elements invoke-args))
            s-args (c/all-possible-values-length-n s-args (c/min-length s-args))]
        (if (c/conformy? s-args)
          (let [args (map vector (:args a*) (c/elements s-args))
                a (if s-args
                    (reduce (fn [a [a-arg s-arg]]
                              (case (:op a-arg)
                                (:binding :local) (let [b (find-binding- a path (:name a-arg))]
                                                    (infer-add-constraint a (:path b) path s-arg))
                                a)) a args)
                    a)
                ;;if (and f-a (= :var f-a-op) (c/fn-spec? s) (not (recursive? a (conj path :fn))))
                ;;(:ret (call-site-specialize f-a f-a-path invoke-args))
                ret-spec (c/invoke s (if (c/valid? (c/invoke-accept s) invoke-args)
                                       invoke-args
                                       (c/invoke-accept s)))]
            (assert ret-spec)
            (assoc-in a (conj path ::ret-spec) ret-spec))
          (assoc-in a (conj path ::ret-spec) (c/invalid {:message (format "infer invoke: can't invoke %s with %s" (print-str s-args) (print-str invoke-args))}))))
      (do
        (println "infer invoke unknown spec:" (:form a*) s)
        (assert false "unknown spec")
        (assoc-in a (conj path ::ret-spec) (c/unknown {:message (format "infer invoke: unknown spec or invalid spec: %s" s)}))))))

(defmethod infer* :local [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        b (find-binding a (pop path) (:name a*))]

    (assert b (format "infer :local: failed to find binding: %s %s %s" (:name a*) (:form a*) (a-loc-str a*)))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (c/spect? (::ret-spec b)))
    (assoc-in a (conj path ::ret-spec) (::ret-spec b))))

(defn fn-fixed-arities
  "Given an :fn, returns a set of ints, the number of required params for each :fn-method"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :fn (:op a*)))]
    (->> a* :methods
         (map :fixed-arity)
         (set))))

(defn fn-variadic-method-requires-arg?
  "True if this fn is variadic, and the method requires a rest
  argument in order to be invoked, because there is another method
  with the same fixed arity"
  [a path]

  (let [a* (get-in a path)
        _ (assert (-> a* :op (= :fn)))
        max-fixed (:max-fixed-arity a*)]
    (and (:variadic? a*)
         (> (count (:methods a*)) 1)
         (->>
          a*
          :methods
          (filter (fn [m]
                    (= max-fixed (:fixed-arity m))))
          (count)
          (= 2)))))

(defn infer-fn-method-spec
  "add the initial fn-spec for this fn-method.

This is called inside infer :fn, so variadic args will get their internal `cat` applied"
  [a path]
  {:post [(every? ::ret-spec (get-in % (conj path :params)))]}
  (let [a* (get-in a path)
        _ (assert a*)
        _ (assert (:op a*))
        _ (assert (= :fn-method (:op a*)))
        a (update-in a (conj path :params)
                     (fn [params]
                       (let [params (mapv (fn [p]
                                            (let [s (cond
                                                      ;; We would like to trust type hints, but they're not validated by the compiler,
                                                      ;; which means they can be wrong.
                                                      ;; (and (:tag p) (not= Object)) (c/class-spec (:tag p))
                                                      :else (c/pred-spec #'any?))
                                                  s (assoc s :inferred true)]
                                              (assoc p ::ret-spec s))) params)
                             params (if (:variadic? a*)
                                      (let [ret-spec (if (fn-variadic-method-requires-arg? a (-> path pop pop))
                                                       (c/cat- [(c/pred-spec #'any?) (c/seq- (c/pred-spec #'any?))])
                                                       (c/cat- [(c/seq- (c/pred-spec #'any?))]))
                                            ret-spec (assoc ret-spec :inferred true)]
                                        (assoc-in params [(-> params count dec) ::ret-spec] ret-spec))
                                      params)]
                         params)))
        args-spec (c/cat- (mapv ::ret-spec (get-in a (conj path :params))))
        fn-spec (c/fn-spec args-spec (c/pred-spec #'any?) nil)
        a (assoc-in a (conj path ::ret-spec) fn-spec)]
    a))

(defmethod infer* :fn [a path]
  (let [a* (get-in a path)
        ;; before walking the fn methods, set up specs for the fn-methods in case there's any self calls
        a (reduce (fn [a method-index]
                    (assert (get-in a (conj path :methods method-index)))
                    (infer-fn-method-spec a (conj path :methods method-index))) a (range (count (:methods a*))))
        a* (get-in a path)
        ret-spec (c/merge-fn-specs (map ::ret-spec (:methods a*)))
        a (assoc-in a (concat path [::ret-spec]) ret-spec)
        _ (assert (c/fn-spec? ret-spec))
        a (if (:local a*)
            (assoc-in a (concat path [:local ::ret-spec]) ret-spec)
            a)
        a (infer-walk a path)
        a* (get-in a path)
        _ (println "infer fn:" (:form a*) (map ::ret-spec (:methods a*)) "=>" (c/merge-fn-specs (map ::ret-spec (:methods a*))))
        spec (assoc (c/merge-fn-specs (map ::ret-spec (:methods a*))) :inferred true)]
    (assoc-in a (conj path ::ret-spec) spec)))

(defmethod infer* :fn-method [a path]
  (let [a* (get-in a path)
        _ (assert (every? ::ret-spec (get-in a (conj path :params))))
        a (infer-walk a path)
        params (get-in a (conj path :params))

        a* (get-in a path)
        params-spec (c/cat- (mapv ::ret-spec params))
        body-ret-spec (-> a* :body ::ret-spec strip-control-flow)
        ret-spec (assoc (c/fn-spec params-spec body-ret-spec nil) :inferred true)
        a (assoc-in a (conj path ::ret-spec) ret-spec)]
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
             (::ret-spec a*) a*
             (:init a*) (assoc a* ::ret-spec (::ret-spec (:init a*)))
             (= :binding (:op a*)) (assoc a* ::ret-spec (assoc (c/pred-spec #'any?) :inferred true))
             (= :catch (:local a*)) (assoc a* ::ret-spec (c/class-spec (:tag a*)))
             (= :this (:local a*)) (let [this (find-this a path)
                                         ret-spec (::ret-spec this)]
                                     (assert (c/spect? ret-spec))
                                     (assoc a* ::ret-spec ret-spec))
             :else (assert false (:op a*)))]
    (assert (::ret-spec a*))
    (assoc-in a (conj path ::ret-spec) (::ret-spec a*))))

(defmethod infer* :do [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        ret-spec (or (some c/throw? (:statements a*)) (-> a* :ret ::ret-spec))]
    (assoc-in a (conj path ::ret-spec) ret-spec)))

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
                                          (infer-add-constraint a (:path b) path spec))
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
  [a path]
  {:post [(::ret-spec (get-in % path))]}
  (let [a* (get-in a path)
        {:keys [class method instance]} a*
        a (maybe-flow-multi-method a path)]
    (if (and class method)
      (let [cls-arg (if (:instance a*)
                      (-> a* :instance ::ret-spec)
                      (-> a* :class (c/value)))
            invoke-args (c/cat- (concat [cls-arg] (mapv (fn [arg] (::ret-spec arg)) (:args a*))))
            methods (get-java-method class method)
            method-specs (map (fn [m]
                                [m (method->spec m)]) methods)
            transformed-spec (->> method-specs
                                  (map (fn [[m s]]
                                         (let [args (infer-invoke-constraints (:args s) (c/elements invoke-args))]
                                           (when (c/conformy? args)
                                             [m (assoc s :args args)]))))
                                  (filter identity)
                                  (map (fn [[m s]]
                                         (c/maybe-transform-method m s (if (c/valid? (:args s) invoke-args)
                                                                         invoke-args
                                                                         (c/invoke-accept s)))))
                                  ((fn [ss]
                                     (if (seq ss)
                                       (c/merge-fn-specs ss)
                                       (do
                                         (println "infer-java invalid" (:form a*) class method method-specs (print-str invoke-args))
                                         (c/invalid {:message (format "infer-java: can't invoke %s %s with %s" class method (print-str invoke-args))}))))))
            ret-spec (if (c/fn-spec? transformed-spec)
                       (:ret transformed-spec)
                       (do
                         (assert (c/invalid? transformed-spec))
                         transformed-spec))
            a (if (c/conformy? transformed-spec)
                (let [spec-args (c/all-possible-values-length-n (:args transformed-spec) (inc (count (:args a*))))
                      arg-pairs (map vector (concat [(:instance a*)] (:args a*)) (c/elements spec-args))]
                  (reduce (fn [a [arg s]]
                            (case (:op arg)
                              (:binding :local) (let [b (find-binding- a path (:name arg))]
                                                  (infer-add-constraint a (:path b) path s))
                              a)) a arg-pairs))
                a)]
        (assoc-in a (conj path ::ret-spec) ret-spec))
      (do
        (println "infer java call:" (:form a*) class method instance "unknown")
        (assoc-in a (conj path ::ret-spec) (c/unknown {:message (format "no spec on reflection: %s" (:form a))}))))))

(defmethod infer* :instance-call [a path]
  {:post [(::ret-spec (get-in % path))]}
  (let [a (infer-walk a path)]
    (infer-java-call a path)))

(defmethod infer* :static-call [a path]
  {:post [(::ret-spec (get-in % path))]}
  (let [a (infer-walk a path)]
    (infer-java-call a path)))

(defn if-test-constraints
  "Given an :if, return two path-constraints, one for the :test being truthy, and one for it being falsey.

   Returns empty constraints if we can't parse the test, or if it
  refers to things we can't constrain (i.e. vars outside of `a`)"
  [a path]
  (let [a* (get-in a path)
        test (if-test a path)
        test-type (if-test-type a path)]
    (if (not= :unknown test-type)
      (let [test-pred (condp = test-type
                        :nil  (c/pred-spec #'nil?)
                        :pred (c/pred-spec (-> test :fn :var))
                        :truthy (c/pred-spec #'identity)
                        :instance? (c/class-spec (-> test :class)))
            ;; the thing we're invoking/testing
            test-arg-a (case test-type
                         (:nil :pred) (-> test :args first)
                         :truthy test
                         :instance? (-> test :target)
                         :unknown nil)
            ;;
            b-path (when (= :local (:op test-arg-a))
                                (let [b (find-binding a path (:name test-arg-a))]
                                  (assert b)
                                  (assert (:path b))
                                  (:path b)))]
        (if b-path
          (condp = test-type
            :pred [[b-path test-pred] [b-path (c/not- test-pred)]]
            :nil [[b-path (c/value nil)] [b-path (c/not- test-pred)]]
            :truthy [[b-path (c/and- [(c/not- (c/pred-spec #'nil?)) (c/not- (c/pred-spec #'false?))])]
                     [b-path (c/or- [(c/pred-spec #'nil?) (c/pred-spec #'false?)])]]
            :instance? [[b-path test-pred]
                        [b-path (c/not- test-pred)]])
          [[] []])))))

(defn if-branch-prediction
  "Predicts whether a branch has to be taken in order to not error out. Returns :then :else or :ambiguous"
  [a path]
  {:post [(contains? #{:then :else :ambiguous} %)]}
  (let [a* (get-in a path)
        {:keys [test target else]} a*]
    (if else
      (cond
        (-> test ::ret-spec (c/throw?)) :else
        (-> else ::ret-spec (c/throw?)) :then
        true :ambiguous)
      :then)))

(defn merge-if-bindings
  "Given an :if at path, combine any bindings and update the original"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :if (:op a*)))
        test-target (if-test-binding a path)
        [[_ test-then-constraint], [_ test-else-constraint]] (if-test-constraints a path)
        bindings-map (->> [:then :else]
                          (map (fn [branch]
                                 [branch (-> a
                                             (get-in (conj path branch :if-bindings))
                                             (->> (group-by :path)))]))
                          (into {}))
        else? (boolean (get-in a (conj path :else)))
        test-then-binding (when test-target
                            (merge (find-binding a (conj path :then) (:name (get-in a test-target))) {:call-path (conj path :then)
                                                                                                      :constraint test-then-constraint}))
        test-else-binding (when (and test-target else?)
                            (merge (find-binding a (conj path :else) (:name (get-in a test-target))) {:call-path (conj path :else)
                                                                                                      :constraint test-else-constraint}))
        bindings-map (if test-then-binding
                       (update-in bindings-map [:then test-target] (fnil conj []) test-then-binding)
                       bindings-map)
        bindings-map (if (and test-target else?)
                       (update-in bindings-map [:else test-target] (fnil conj []) test-else-binding)
                       bindings-map)
        predicted-branch (if-branch-prediction a path)
        get-other-branch (fn [branch]
                           (case branch
                             :then :else
                             :else :then))
        update-bindings (fn [a branch]
                          {:pre [(#{:then :else} branch)]}
                          (let [[test-this-constraint test-other-constraint] (if (= branch :then)
                                                                               [test-then-constraint test-else-constraint]
                                                                               [test-else-constraint test-then-constraint])]
                            (reduce (fn [a [b-path this-bindings]]
                                      (let [this-branch branch
                                            other-branch (get-other-branch branch)
                                            this-constraints (c/and- (map :constraint this-bindings))]
                                        (if (= test-target b-path)
                                          (let [other-bindings (get-in bindings-map [other-branch b-path])
                                                other-constraints (c/and- (map :constraint other-bindings))]
                                            (cond
                                              (and other-constraints (= predicted-branch :ambiguous)) (infer-add-constraint a b-path
                                                                                                                         path
                                                                                                                         (c/or- [this-constraints other-constraints]))
                                              (or (= predicted-branch this-branch) (not other-constraints)) (reduce (fn [a {:keys [call-path constraint] :as binding}]
                                                                                                                      (if (c/valid? test-this-constraint constraint)
                                                                                                                        a
                                                                                                                        (infer-add-constraint a b-path call-path constraint))) a this-bindings)
                                              :else a))
                                          (infer-add-constraint a b-path path this-constraints)))) a (get bindings-map branch))))]
    (-> a
        (update-bindings :then)
        (update-bindings :else))))

(defmethod infer* :if [a path]
  (let [a (assoc-in a (conj path :then :if-bindings) [])
        a (if (get-in a (conj path :else))
            (assoc-in a (conj path :else :if-bindings) [])
            a)
        a (walk-if infer-walk a path)]
    (merge-if-bindings a path)))

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
                                (infer-add-constraint a b-path path (::ret-spec e)))
            a)]
    (assoc-in a (conj path ::ret-spec) (c/throw-form (::ret-spec e)))))

(defmethod infer* :keyword-invoke [a path]
  (let [a (infer-walk a path)
        a* (get-in a path)
        target (:target a*)
        a (case (:op target)
            (:binding :local) (let [b (find-binding a path (:name target))]
                                (assert (:path b))
                                (infer-add-constraint a (:path b) path (c/or- [(c/pred-spec #'nil?) (c/pred-spec #'map?) (c/pred-spec #'set?)])))
            a)]
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
               (get-var-spec v a path))
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
                                            (infer-add-constraint a (:path b) path s))
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
                          (infer-add-constraint a b-path path (::ret-spec (:val a*))))
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
