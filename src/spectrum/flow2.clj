(ns spectrum.flow2
  (:require [clojure.core.memoize :as memo]
            [clojure.data :refer [diff]]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.string :as str]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer :as analyzer]
            [spectrum.analyzer-spec]
            [spectrum.conform2 :as c]
            [spectrum.core-specs]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.java :as j]
            [spectrum.protocols :as p]
            [spectrum.queue :as q]
            [spectrum.topo-sort :as topo-sort]
            [spectrum.util :as util :refer [print-once protocol? namespace? queue validate! instrument-ns memoize-with]]
            [spectrum.unify :as u])
  (:import [clojure.lang Var Namespace]))

(s/def ::a ::ana.jvm/analysis)

(s/def ::path-elem (s/or :k keyword? :i nat-int?))
(s/def ::path (s/coll-of ::path-elem :type vector?))

(def type-counter (atom -1))

(s/def ::context (s/keys :req-un []))
(defn new-context []
  {:typenames (atom {})})

(defn new-type []
  (let [next (swap! type-counter inc)]
    (symbol (str "?" next))))

(s/fdef a-loc :args (s/cat :a (s/nilable ::ana.jvm/analysis)) :ret (s/keys :opt-un [:ana.jvm.env/file :ana.jvm.env/line :ana.jvm.env/column]))
(defn a-loc [a]
  (select-keys a [:file :line :column]))

(defn store-type! [context t a path]
  (let [a* (get-in a path)
        {:keys [form op]} a*
        t (with-meta t {::form form
                        ::op op
                        ::loc (a-loc a*)})]
    (-> context :typenames (swap! assoc [a path] t))))

(defn analyze-form
  "Analyze a form.

   (analyze-form '(string? 3))

   Optionally takes a map of keywordized variables to specs:

   (analyze-form '(string? x) {:x (c/pred-spec #'string?)})
  "
  ([form]
   (analyze-form form {}))
  ([form specs]
   (let [locals (into {} (map (fn [[binding s]]
                                (let [binding (symbol (name binding))]
                                  [binding {:op :binding
                                            :name binding
                                            :form binding
                                            :env {}
                                            :local :let
                                            :atom (atom {::t (new-type)})
                                            ::ret-spec s
                                            }])) specs))]
     (analyzer/analyze form (assoc (ana.jvm/empty-env) :locals locals)))))

(defn walk-a
  "Given an analysis a, call f on all of a's `:children` (non-recursive)"
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

(defn walk-a-rec
  "Given an analysis a, recursively call f on all of a's `:children`, and also `a` when `path` not provided. Return a seq of all `f` return values"
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

(defn create-typename-dispatch [context a path]
  (:op (get-in a path)))

(defmulti create-typename #'create-typename-dispatch)

(defmethod create-typename :default [context a path]
  (store-type! context (new-type) a path))

(defmethod create-typename :binding [context a path]
  (let [t (new-type)
        a* (get-in a path)]
    (assert (:atom a*))
    (swap! (:atom a*) assoc ::t t ::path path)
    (store-type! context t a path)
    t))

(defmethod create-typename :local [context a path]
  (store-type! context (new-type) a path))

(defmethod create-typename :fn [context a path]
  ;; we need an extra type on the :ret of a fn, in case it is called locally
  (let [fn-t (new-type)
        ret-t (new-type)
        a* (get-in a path)]
    (store-type! context fn-t a path)
    (store-type! context ret-t a (conj path :ret))
    fn-t))

(defmethod create-typename :fn-method [context a path]
  (let [fn-t (new-type)
        ret-t (new-type)
        a* (get-in a path)]
    (store-type! context fn-t a path)
    (store-type! context ret-t a (conj path :ret))
    fn-t))

(defn assign-typenames
  "Walk the analysis, assign type names to every expression"
  [context a]
  (walk-a-rec (fn [a path]
                (create-typename context a path)) a))

(defn get-equations-dispatch [context a path]
  (:op (get-in a path)))

(s/def ::equation* (s/tuple ::c/type ::c/type))

(defn well-formed-equation? [x]
  (let [[a b] (s/unform ::equation* x)]
    (if (or (c/logic? a)
              (c/logic? b))
      (c/logic? a)
      true)))

(s/def ::equation (s/and ::equation*
                         well-formed-equation?))
(s/def ::equations (s/coll-of ::equation))

(defmulti get-equations* #'get-equations-dispatch)

(defmethod get-equations* :default [context a path]
  (let [a* (get-in a path)]
    (assert a*)
    (println "no equations for" (:form a*) (:op a*))
    (assert false))
  [])

(defn get-type-dispatch [context a path]
  (-> a (get-in path) :op))

(defmulti get-type* #'get-type-dispatch)

(defmethod get-type* :default [context a path]
  (-> context :typenames deref (get [a path])))

(defmethod get-type* :local [context a path]
  {:pre [a (get-in a path)]
   :post [%]}
  (let [a* (get-in a path)]
    (assert a*)
    (or (-> a* :atom deref ::t)
        ;; workaround https://dev.clojure.org/jira/browse/TANAL-127
        (-> a* :env :locals (get (:name a*)) :atom deref ::t))))

(s/fdef get-type :ret (s/nilable ::c/type))
(defn get-type [context a path]
  (get-type* context a path))

(s/fdef get-type! :ret ::c/type)
(defn get-type! [context a path]
  {:post [(do (when-not %
                (println "get-type!" (:form a) path "failed")) true)
          %]}
  (get-type* context a path))

(defn ensure-type!
  "Create or return the existing type at [a path]"
  [context a path]
  (if-let [t (get-type context a path)]
    t
    (let [t (new-type)]
      (println "storing new type" t "for" path)
      (store-type! context t a path)
      t)))

(defmethod get-equations* :const [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/value-t (:form a*))]]))

(defmethod get-equations* :binding [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (cond
      (::ret-spec a*) [[t (::ret-spec a*)]]
      (:init a*) [[t (get-type! context a (conj path :init))]]
      :else [])))

(defmethod get-equations* :local [context a path]
  ;; workaround https://dev.clojure.org/jira/browse/TANAL-127
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (if-let [binding (-> a* :env :locals (get (:name a*)))]
      (do
        (assert (::ret-spec binding))
        [[t (::ret-spec binding)]])
      [])))

(defmethod get-equations* :var [context a path]
  [])

(defmethod get-equations* :quote [context a path]
  [])

(defn map-sequential-children
  "Call `(f context a $path)` on each sequential child of (-> a (get-in path) key)"
  [f context a path key]
  (map (fn [i]
         (f context a (conj path key i))) (-> a (get-in (conj path key)) count range)))

(defmethod get-equations* :def [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t #'var?]]))

(defn get-recur-paths
  "Given a node at `[a path]`, return all `recur` nodes in the tree. Stops at loops/inner fns"
  [a path]
  (let [a* (get-in a path)]
    (->> a*
         :children
         (mapcat (fn [c]
                   (let [new-path (conj path c)
                         c-node (get-in a new-path)]
                     (if (or (= :recur (:op c-node))
                             (= :fn-method (:op c-node)))
                       [new-path]
                       (if (sequential? c-node)
                         (mapcat (fn [i]
                                   (get-recur-paths a (conj new-path i))) (range (count c-node)))
                         (get-recur-paths a new-path)))))))))

(defmethod get-equations* :fn-method [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        ret-type (get-type! context a (conj path :body))
        arg-ts (map-sequential-children get-type! context a path :params)
        ;; TODO look up fn spec here and apply
        ;; don't bother applying #'any? to params unless we have specs, because any is annoying to unify atm
        ;; arg-eqs (map (fn [t]
        ;;                [t #'any?]) arg-ts)
        ;; recur-paths (get-recur-paths a path)
        ]
    (concat
     ;; arg-eqs
     [[t (c/fn-t {(c/cat-t arg-ts)
                 ret-type})]
     [ret-t ret-type]])))

(defmethod get-equations* :fn [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        fn-type (c/or-t (map-sequential-children get-type! context a path :methods))
        ret-type (c/or-t (map-sequential-children (fn [context a path]
                                                   (get-type! context a (conj path :ret))) context a path :methods))]
    [[t fn-type]
     [ret-t ret-type]]))

(defmethod get-equations* :let [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :body))]]))

(defmethod get-equations* :do [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :ret))]]))

(defmethod get-equations* :try [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        body-t (get-type! context a (conj path :body))
        catches-t (map-sequential-children (fn [context a p]
                                             (get-type! context a p)) context a path :catches)
        finally-t (when (get-in a (conj path :finally))
                    (get-type! context a (conj path :finally)))
        ret-t (c/or-t (concat [body-t finally-t] catches-t))]
    [[t ret-t]]))

(defmethod get-equations* :catch [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ex (get-in a (conj path :class :val))
        _ (assert (class? ex))
        ex-class-spec (c/class-t ex)]
    [[t ex-class-spec]
     [(get-type! context a (conj path :local)) ex-class-spec]]))

(defmethod get-equations* :map [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-keys (reduce (fn [ret-keys i]
                           (let [k-path (conj path :keys i)
                                 k (get-in a k-path)
                                 v-path (conj path :vals i)
                                 v (get-in a v-path)]
                             (assert k)
                             (assert v)
                             (if (and (= :const (:op k)) (-> k :val (keyword?)))
                               (let [key-type (if (qualified-keyword? (:val k))
                                                :req
                                                :req-un)]
                                 (assoc-in ret-keys [key-type (:val k)] (get-type! context a v-path)))
                               ret-keys)))
                         {:req {}
                          :req-un {}} (range (count (:keys a*))))
        ret-t (c/keys-t (:req ret-keys) (:req-un ret-keys) {} {})]
    [[t ret-t]]))

(defn resolve-java-class-spec [x]
  (c/class-t (j/resolve-java-class x)))

(defmethod get-equations* :static-field [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (j/get-java-field class field {:static? true})
        s (resolve-java-class-spec (:type f))]
    (assert s)
    [[t s]]))

(defmethod get-equations* :with-meta [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :expr))]]))

(s/fdef get-java-method :args (s/cat :cls class? :method symbol?) :ret (s/coll-of j/reflect-method?))
(defn get-java-method
  "Return all arities"
  [cls method]
  (some->> (reflect/reflect cls)
           :members
           (filterv (fn [m]
                      (and (instance? clojure.reflect.Method m)
                           (= method (:name m)))))))

(s/fdef method-class->t :args (s/cat :c class?) :ret ::c/type)
(defn method-class->t
  "Given an argument or return class from a java method, return a ::type"
  [c]
  (cond
    (j/primitive? c) (c/class-t c)
    (= c clojure.lang.ISeq) (c/seq-of #'any?)
    :else (c/or-t [(c/class-t c) #'nil?])))

(s/def :method/paramter-types (s/coll-of (s/or :c class? :n nil?)))
(s/def :method/return-types (s/or :c class? :n nil?))
(s/def ::method (s/keys :req-un [:method/parameter-types :method/return-type]))

(s/fdef method->t :args (s/cat :m ::method) :ret ::c/type)
(defn method->t
  "Given a java method, translate it to a type, and add s/nilable to arguments & return type as necessary"
  [m]
  (let [{:keys [parameter-types declaring-class return-type name]} m
        declaring-class (j/resolve-java-class declaring-class)]
    (or
     (data/get-updated-method-spec declaring-class
                                   (:name m)
                                   (mapv j/resolve-java-class parameter-types))
     (c/fn-t {(c/cat-t (mapv (fn [param]
                               (-> param j/resolve-java-class method-class->t)) parameter-types))
              (-> return-type j/resolve-java-class method-class->t)}))))

(defn make-equations
  "Given two types that are `valid?`, return a set of equations"
  [a b]
  (when-not (and (c/cat-t? a) (c/cat-t? b))
    (println "make-eq" a b))
  (assert (c/cat-t? a))
  (assert (c/cat-t? b))
  (mapv (fn [ma ia]
          [ma ia]) (rest a) (rest b)))

(s/fdef get-equations-java-call :ret ::equations)
(defn get-equations-java-call [context a path]
  (let [a* (get-in a path)
        {:keys [class method instance]} a*]
    (if (and class method)
      (let [cls-arg (if (:instance a*)
                      (get-type! context a (conj path :instance))
                      (-> a* :class (c/value-t)))
            invoke-args (c/cat-t (map-sequential-children get-type! context a path :args))
            ret-t (get-type! context a path)
            methods (get-java-method class method)
            method-t (->> methods
                          (map method->t)
                          (filter (fn [t]
                                    (c/fn-method-unifying t invoke-args)))
                          (c/merge-fns))
            args-cat (-> method-t (c/fn-args) (c/all-possible-values-length-n (c/cat-length invoke-args)))
            eqs (if method-t
                  (conj (make-equations invoke-args args-cat)
                        [ret-t (c/fn-ret method-t)])
                  [])]
        eqs)
      (do
        (println "infer java call:" (:form a*) class method instance "unknown")
        []))))

(defmethod get-equations* :static-call [context a path]
  (get-equations-java-call context a path))

(defmethod get-equations* :instance-call [context a path]
  (get-equations-java-call context a path))

(defn analyze-cache-a [a]
  (walk-a-rec (fn [a path]
                (let [a* (get-in a path)]
                  (when (= :def (:op a*))
                    (data/store-var-analysis (:var a*) a path)))) a))

(defn analyze-cache-ns [ns]
  (let [env (ana.jvm/empty-env)
        as (analyzer/analyze-ns-1 ns env)]
    (dorun (map analyze-cache-a as))))

(defn ensure-analysis [ns]
  (try
    (when-not (data/analyzed-ns? ns)
      (data/mark-ns-analyzed! ns)
      (println "analyzing" ns)
      (binding [*warn-on-reflection* false]
        (analyze-cache-ns ns)))
    (catch Throwable t
      (data/mark-ns-unanalyzed! ns)
      (throw t))))

(defn ensure-analysis-var [v]
  (ensure-analysis (.ns v)))

(defn invoke-get-fn-analysis-var [v]
  (ensure-analysis-var v)
  (data/get-var-analysis v))

(s/fdef get-analysis-for-invoke :args (s/cat :a ::ana.jvm/analysis :p ::path) :ret (s/keys :req-un [::a ::path]))
(defn get-analysis-for-invoke
  "Given an invoke at [a path], return the analysis of the thing being invoked"
  [a path]
  (let [a* (get-in a path)
        f (:fn a*)
        [fn-op path*] (or (when (-> a* :fn :op)
                            [(-> a* :fn :op) (conj path :fn)])
                          [(-> a* :op) path])
        ret (condp = fn-op
              :var (invoke-get-fn-analysis-var (-> a* :fn :var))
              :the-var (invoke-get-fn-analysis-var (-> a* :fn :var))
              :fn  {:a (-> a* :fn) :path (conj path :fn) :op fn-op}
              :local (let [b-path (-> a* :fn :atom deref (get ::path))
                           _ (assert b-path)
                           b (get-in a b-path)]
                       (assert b)
                       {:a a
                        :path (:path b)
                        :op fn-op})
              :const {:a (-> a* :fn :val)
                      :path (conj path :fn)
                      :op fn-op}
              :instance-field {:a a :path path* :op fn-op}
              :invoke (get-analysis-for-invoke a (conj path :fn))
              :keyword-invoke {:a a :path path* :op fn-op}
              :with-meta (get-analysis-for-invoke a (conj path :fn :expr))
              :set {:a a :path path* :op fn-op}
              :map {:a a :path path* :op fn-op}
              :if {:a a :path path* :op :if}
              (do
                (println "invoke-get-fn-analysis" (:form a*) (:op a*))
                (assert false (format "don't know how to find analysis for %s" fn-op))))]
    ret))

(defn get-type-for-invoke
  "Return the type for the thing being invoked at `[a path]`"
  [a path]
  (let [a* (get-in a path)
        v (get-in a (concat path [:fn :var]))]
    (or (when v
          (or ;;(c/get-var-spec v)
              (data/get-var-spec v)))
        (assert false (format "get-spec-for-invoke couldn't find spec for %s" (:form a*))))))

(defn a-def-paths
  "Returns a seq of paths, one for each `:def` node in this analysis"
  [a]
  (->>
   (walk-a-rec (fn [a path]
                 (when (= :def (get-in a (conj path :op)))
                   path)) a)
   (filter identity)))

(defn invoke-local?
  "Returns true if the invoke at [a path] is a local fn contained within a"
  [a path]
  (let [a* (get-in a (conj path :fn))
        op (:op a*)]
    (contains? #{:local :fn} op)))

(defn get-eq-invoke-spec
  "get-equations for invoking something with a spec"
  [context a path]
  (let [a* (get-in a path)
        args (:args a*)
        invoke-args (c/cat-t (map-sequential-children get-type! context a path :args))
        t (get-type-for-invoke a path)
        ret-t (get-type! context a path)
        t-args (c/all-possible-values-length-n (c/fn-args t) (c/cat-length invoke-args))]
    (assert t)
    (->>
     (conj
      (make-equations invoke-args t-args)
      [ret-t (c/fn-ret t)]))))

(defn fn-get-method-with-arity
  "Given an :fn node at `[a path]`, return the path to the method that
  will be invoked if called with n arguments"
  [a path n]
  (let [a* (get-in a path)
        p (conj path :methods)
        method-count (count (get-in a (conj path :methods)))]
    (->> (range 0 method-count)
         (filter (fn [i]
                   (let [m (get-in a (conj path :methods i))
                         {:keys [fixed-arity variadic?]} m]
                     (or (= n fixed-arity)
                         variadic?))))
         first
         ((fn [i]
            (if i
              (conj path :methods i)
              nil))))))

(defn get-eq-invoke-local-fn [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        f (get-type! context a (conj path :fn))
        invoke-args (c/cat-t (map-sequential-children get-type! context a path :args))
        ;; fn-args-t (c/all-possible-values-length-n (c/fn-args t) (c/cat-length invoke-args))
        method-path (fn-get-method-with-arity a (conj path :fn) (count (get-in a (conj path :args))))
        m (get-in a method-path)
        fn-args-t (c/cat-t (map-sequential-children get-type! context a method-path :params))
        ret-t (get-type! context a (conj path :fn :ret))]

    (assert f)
    (assert ret-t)
    (conj (make-equations invoke-args fn-args-t)
          [t ret-t])))

(defn self-var-call?
  "True if the invoke at [a path] is a call to a var defined in a. Returns the path to the :def or nil"
  [a path]
  (let [a* (get-in a (conj path :fn))
        op (:op a*)]
    (when-let [v (:var a*)]
      (->> (a-def-paths a)
           (filter (fn [p]
                     (= v (get-in a (conj p :var)))))
           (first)))))

(defn maybe-with-meta
  "Given a path, if [a path] is a :with-meta node, return the real path"
  [a path]
  (if (= :with-meta (get-in a (conj path :op)))
    (conj path :expr)
    path))

(defn get-eq-invoke-self-var [context a path]
  (let [t (get-type! context a path)
        var-path (self-var-call? a path)
        var-fn-ret-path (-> var-path (conj :init) (#(maybe-with-meta a %)) (conj :ret))]
    [[t (get-type! context a var-fn-ret-path)]]))

(defmethod get-equations* :invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (cond
      (invoke-local? a path) (get-eq-invoke-local-fn context a path)
      (self-var-call? a path) (get-eq-invoke-self-var context a path)
      :else (get-eq-invoke-spec context a path))))

(defmethod get-equations* :if [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (if (get-in a (conj path :else))
      [[t (c/or-t [(get-type! context a (conj path :then))
                   (get-type! context a (conj path :else))])]]
      [[t (get-type! context a (conj path :then))]])))

(defmethod get-equations* :throw [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/throw-t (get-type! context a (conj path :exception)))]]))

(defmethod get-equations* :new [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/class-t (get-type! context a (conj path :class)))]]))

(defn find-loop-path
  "Given a recur at `path`, return the path to the recur destination"
  [a path]
  (loop [path path]
    (let [a* (get-in a path)]
      (if (contains? #{:loop :fn-method} (:op a*))
        path
        (if (seq path)
          (recur (pop path))
          (assert false (format "couldn't find loop in %s" (:form a))))))))

(defmethod get-equations* :recur [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        dest-path (find-loop-path a path)
        recur-args (map-sequential-children get-type! context a path :exprs)
        dest-op (get-in a (conj dest-path :op))
        _ (assert dest-op)
        dest-arg-key ({:fn-method :params
                       :loop :bindings} dest-op)
        _ (assert dest-arg-key)
        dest-args (map-sequential-children get-type! context a dest-path dest-arg-key)]
    (if (= (count recur-args) (count dest-args))
      [] ;; (mapv (fn [d r]
         ;;         [d (c/maybe-t r)]) dest-args recur-args)
      [(c/invalid {:message (format  "mismatch recur args: %s vs. %s" (count recur-args) (count dest-args))})])))

(defmethod get-equations* :instance? [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO return value true/false when we know the check is true
    [[t (c/class-t Boolean/TYPE)]]))

(defmethod get-equations* :vector [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/cat-t (map-sequential-children get-type! context a path :items))]]))

(defmethod get-equations* :loop [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :body))]]))

(defmethod get-equations* :protocol-invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO verify arg count
    [[t #'any?]
     [(get-type! context a (conj path :target)) (c/protocol-t (-> a* :protocol))]]))

(defmethod get-equations* :keyword-invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO more specific, validate arg count
    [[t #'any?]]))

(defmethod get-equations* :instance-field [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (j/get-java-field class field)]
    [[t (resolve-java-class-spec (:type f))]]))

(defmethod get-equations* :set [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/value-t (map-sequential-children get-type! context a path :items))]]))

(s/fdef get-equations :args (s/cat :c ::context :a ::a) :ret ::equations)
(defn get-equations [context a]
  (->> (walk-a-rec (fn [a path]
                     (let [a* (get-in a path)
                           _ (assert a*)
                           {:keys [form op]} a*]
                       (->> (get-equations* context a path)
                            ((fn [eqs]
                               (validate! ::equations eqs {:form (:form a*)})
                               (when (seq eqs)
                                 (println "get-eq" (:op a*) (:form a*) "=>" eqs))
                               eqs))
                            (mapv (fn [e]
                                    (with-meta e (merge {::form form
                                                         ::op op}
                                                        (a-loc a*)))))))) a)
       (apply concat)
       (doall)))

(s/fdef consolidate-equations :args (s/cat :eq ::equations) :ret ::equations)
(defn consolidate-equations [eqs]
  {:post [(do (println "consolidate-eq:" eqs "=>" %) true)]}
  (->> eqs
       (group-by (fn [eq] (first eq)))
       (mapcat (fn [[l eqs]]
                 (let [logic-eqs (filter (fn [[l r]]
                                           (c/logic? r)) eqs)
                       constraint-eqs (remove (fn [[l r]]
                                                (c/logic? r)) eqs)]
                   (->>
                    (concat
                     logic-eqs
                     (when (seq constraint-eqs)
                       [(-> [l (c/and-t (map second constraint-eqs))]
                            (with-meta {::constraints (mapv (fn [eq]
                                                              {:meta (meta eq)
                                                               :constraint (second eq)}) constraint-eqs)}))]
                       ;;(println "consolidate eqs:" l constraint-eqs)
                       ))
                    (filterv identity)))))
       (doall)))

(defn logic-n
  "If v is a logic variable, return its number, else nil"
  [v]
  (when (c/logic? v)
    (let [[_ n] (re-find #"(\d+)$" (name v))]
      (Long/parseLong n))))

(defn compare-variables [v1 v2]
  (if (and (c/logic? v1) (c/logic? v2))
    (compare (logic-n v1) (logic-n v2))
    0))

(defn compare-equations [e1 e2]
  "sort such that lower number variables are first"
  [e1 e2]
  (let [[l1 r1] e1
        [l2 r2] e2]
    (compare-variables l1 l2)))

(defn sort-equations [eqs]
  (sort compare-equations eqs))

(defn unify-all-equations [eqs]
  (let [subst {}]
    (reduce (fn [{:keys [subst fail] :as state} eq]
              (if fail
                state
                (let [[l r] eq]
                  (let [subst* (u/unify l r subst)]
                    (if subst*
                      (assoc state :subst subst*)
                      (assoc state :fail eq)))))) {:subst subst :fail nil} eqs)))

(defn store-var-inference-results [context a subst]
  (->> (a-def-paths a)
       (map (fn [def-p]
              (let [var-a (get-in a def-p)
                    v (get-in a (conj def-p :var))
                    init-p (conj def-p :init)
                    t (get-type! context a init-p)
                    _ (println "store var inference:" subst t)
                    v-s (if t
                          (c/resolve-type t subst)
                          (c/invalid "inference failed" v))
                    v-s (if (and (c/or-t? v-s)
                                 (every? c/fn-t? (rest v-s)))
                          (c/merge-fns (rest v-s))
                          v-s)]
                (println (:form a) def-p init-p "=>" t v-s)
                (assert v-s)
                (println "storing" v v-s)
                (data/store-var-spec v v-s))))
       (dorun)))

(s/fdef a-vars :args (s/cat :v ::ana.jvm/analysis) :ret (s/coll-of var? :kind set?))
(defn a-vars
  "Return all vars referenced in this analysis"
  [a]
  (->> a
       (walk-a-rec (fn [a path]
                     (:var (get-in a path))))
       (filter identity)
       (set)))

(s/fdef v-vars :args (s/cat :v var?) :ret (s/coll-of var? :kind set?))
(defn v-vars
  "Return all vars this var depends on. Analyzes if necessary"
  [v]
  (ensure-analysis-var v)
  (let [{:keys [a]} (data/get-var-analysis v)]
    (if a
      (-> a a-vars (disj v))
      #{})))

(defn var-dependencies
  "Given an analysis, return a dependency map of all vars the analysis depends on"
  [a]
  (loop [dep-map {}
         queue (q/q (a-vars a))]
    (if-let [v (first queue)]
      (let [deps (v-vars v)
            seen (set (keys dep-map))
            new (set/difference deps seen)]
        (recur (assoc dep-map v deps) (pop (apply conj queue new))))
      dep-map)))

(declare infer)

(s/def ::dependencies? (s/nilable boolean?))

(s/fdef infer-var :args (s/cat :v var? :opts (s/? (s/keys :opt-un [::dependencies?]))))
(defn infer-var [v & [{:keys [dependencies?]}]]
  (ensure-analysis-var v)
  (if-let [{:keys [a]} (data/get-var-analysis v)]
    (infer a {:dependencies? dependencies?})
    (println "couldn't find analysis for" v)))

(defn ensure-infer-var [v &[{:keys [dependencies?]}]]
  (or (data/get-var-spec v)
      (infer-var v {:dependencies? dependencies?})))

(defn infer-dependencies
  "Infer all var dependencies contained in analysis a"
  [a]
  (->> a
       (var-dependencies)
       (topo-sort/topo-sort)
       (reverse)
       (map (fn [v]
              (ensure-infer-var v {:dependencies? false})))
       (dorun)))

(defn get-type-meta
  "Given a type lvar, return its metadata"
  [context t]
  (->> context
      :typenames
      deref
      vals
      (filter (fn [t*]
                (= t t*)))
      first
      meta))

(defn debug-all-types [context]
  (->> context
       :typenames
       deref
       set/map-invert
       (sort-by (fn [[t _]]
                  (logic-n t)))
       (map (fn [[t [a path]]]
              (println t (get-in a (conj path :op)) (get-in a (conj path :form)))))
       (dorun)))

(defn debug-failure
  "Given a unify failure, print relevant debugging"
  [context a eqs subst fail]
  (let [[l r] fail
        l-meta (get-type-meta context l)
        existing-l (c/resolve-type l subst)]
    (debug-all-types context)
    (println "infer failed" (:form a) "fail:" fail)
    (println "fail" fail " meta:" (-> fail meta))
    (println "subst" subst)

    (println "expected" l (::form l-meta) "=>" (c/resolve-type r subst))
    (when existing-l
      (println "could not unify" l ":" (::form l-meta) "at" (::loc l-meta)  ":" (c/resolve-type r subst)  "with" existing-l))
    (doseq [lv (u/get-lvars fail)]
      (println lv "=>" (c/resolve-type lv subst)))
    (doseq [lv (u/get-lvars existing-l)]
      (println lv "=>" (c/resolve-type lv subst)))))

(defn valid-subst?
  "True if everything conforms"
  [subst]
  (->> subst
       (vals)
       (every? c/conformy?)))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis :opts (s/? (s/keys :opt-un [::dependencies?]))) :ret (s/nilable ::c/type))
(defn infer [a & [{:keys [dependencies?]
                   :or {dependencies? true}}]]
  (let [context (new-context)]
    (when dependencies?
      (infer-dependencies a))
    (assign-typenames context a)
    (let [eq (get-equations context a)
          eq (consolidate-equations eq)
          eq (sort-equations eq)
          {:keys [subst fail]} (unify-all-equations eq)
          t (get-type! context a [])]
      (if fail
        (debug-failure context a eq subst fail)
        (if (valid-subst? subst)
          (do
            (store-var-inference-results context a subst)
            (c/resolve-type t subst)))))))

(defn infer-form
  ([form]
   (-> form
       (analyze-form)
       infer))
  ([form specs]
   (-> form
       (analyze-form specs)
       infer)))

(instrument-ns)
