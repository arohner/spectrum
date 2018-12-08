(ns spectrum.flow2
  (:require [clojure.core.memoize :as memo]
            [clojure.core.unify :as u]
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
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.flow :as f]
            [spectrum.java :as j]
            [spectrum.protocols :as p]
            [spectrum.queue :as q]
            [spectrum.topo-sort :as topo-sort]
            [spectrum.util :as util :refer [print-once protocol? namespace? queue validate! instrument-ns memoize-with]]
            [spectrum.unify :as u2])
  (:import [clojure.lang Var Namespace]))

(s/def ::a ::ana.jvm/analysis)

(s/def ::path-elem (s/or :k keyword? :i nat-int?))
(s/def ::path (s/coll-of ::path-elem :type vector?))

(def type-counter (atom -1))

(defn new-context []
  {:typenames (atom {})})

(s/def ::type c/spect?)

(defn new-type []
  (let [next (swap! type-counter inc)]
    (c/new-logic next)))

(defn store-type! [context t a path]
  (let [a* (get-in a path)
        {:keys [form op]} a*
        t (with-meta t {::form form
                        ::op op})]
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

(s/def ::equation (s/tuple c/spect? c/spect?))
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

(s/fdef get-type :ret (s/nilable ::type))
(defn get-type [context a path]
  (get-type* context a path))

(s/fdef get-type! :ret ::type)
(defn get-type! [context a path]
  {:post [(do (when-not %
                (println "get-type!" (:form a) path "failed")) true)
          ;; %
          ]}
  (get-type* context a path))

(defn ensure-type!
  "Create or return the existing type at [a path]"
  [context a path]
  (if-let [t (get-type context a path)]
    t
    (let [t (new-type)]
      (store-type! context t a path)
      t)))

(defmethod get-equations* :const [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/value (:form a*))]]))

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
        (println "get-eq local:" t)
        (println "binding:" binding)
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
    [[t (c/pred-spec #'var?)]]))

(defmethod get-equations* :fn-method [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        ret-type (get-type! context a (conj path :body))]
    [[ret-t ret-type]
     [t (c/fn-spec {:args (c/cat- (map-sequential-children get-type! context a path :params))
                    :ret ret-t})]]))

(defmethod get-equations* :fn [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        fn-type (c/or- (map-sequential-children get-type! context a path :methods))
        ret-type (c/or- (map-sequential-children (fn [context a path]
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
        ret-t (c/or- (concat [body-t finally-t] catches-t))]
    [[t ret-t]]))

(defmethod get-equations* :catch [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ex (get-in a (conj path :class :val))
        _ (assert (class? ex))
        ex-class-spec (c/class-spec ex)]
    [[t (c/throw-form ex-class-spec)]
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
        ret-t (c/keys-spec (:req ret-keys) (:req-un ret-keys) {} {})]
    [[t ret-t]]))

(defmethod get-equations* :static-field [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (f/get-java-field class field {:static? true})
        s (f/resolve-java-class-spec (:type f))]
    (assert s)
    [[t s]]))

(defmethod get-equations* :with-meta [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :expr))]]))

(s/fdef infer-invoke-constraints :args (s/cat :s c/spect? :args (s/coll-of c/spect?)) :ret c/spect?)
(defn infer-invoke-constraints
  "Given a spec (which could accept multiple type or arities), and a
  seq of partially constrained argument specs, constrain all
  arguments, returning a spec representing all possible concrete specs
  that args could conform to"
  [spec args]
  {:pre [(validate! c/spect? spec)
         (validate! c/conformy? spec)
         (not (c/spect? args))
         (not (c/fn-spec? spec))
         (validate! (s/coll-of c/spect?) args)]
   :post [(validate! c/spect? %)]}
  (if (not (c/unknown? spec))
    (let [rets (->> (c/all-possible-values spec (count args))
                    (filter (fn [s]
                              (<= (c/min-length s) (count args)))))]
      (if (seq rets)
        (c/or- rets)
        (c/invalid {:message (format "infer-invoke-constraints: can't invoke %s with %s" (print-str spec) (print-str args))})))
    spec))

(s/fdef get-equations-java-call :ret ::equations)
(defn get-equations-java-call [context a path]
  {:post [(do (println "get-eq java" (:form (get-in a path)) "=>" %) true)]}
  (let [a* (get-in a path)
        {:keys [class method instance]} a*]
    (if (and class method)
      (let [cls-arg (if (:instance a*)
                      (get-type! context a (conj path :instance))
                      (-> a* :class (c/value)))
            invoke-args (c/cat- (concat [cls-arg] (map-sequential-children get-type! context a path :args)))
            methods (f/get-java-method class method)
            method-specs (map (fn [m]
                                [m (f/method->spec m)]) methods)
            transformed-spec (->> method-specs
                                  (map (fn [[m s]]
                                         (let [args (infer-invoke-constraints (:args s) (c/elements invoke-args))]
                                           (when (c/conformy? args)
                                             (assoc s :args args)))))
                                  (filter identity)
                                  ((fn [ss]
                                     (if (seq ss)
                                       (c/merge-fn-specs ss)
                                       (do
                                         (println "infer-java invalid" (:form a*) class method invoke-args)
                                         (assert false)
                                         (c/invalid {:message (format "infer-java: can't invoke %s %s with %s" class method (print-str invoke-args))}))))))
            ret-spec (if (c/fn-spec? transformed-spec)
                       (:ret transformed-spec)
                       (do
                         (assert (c/invalid? transformed-spec))
                         transformed-spec))]
        (println "spec:" transformed-spec)
        (if (c/conformy? transformed-spec)
          (let [spec-args (c/all-possible-values-length-n (:args transformed-spec) (inc (count (:args a*))))
                arg-pairs (map vector (concat [(:instance a*)] ) (c/elements spec-args))]
            (->>
             (concat
              (if-let [inst (get-in a (conj path :instance))]
                [[(get-type! context a (conj path :instance)) (first (c/elements spec-args))]]
                [])
              (map (fn [i s]
                     (let [arg-type (get-type! context a (conj path :args i))]
                       [arg-type s]))
                   (range (count (:args a*))) (rest (c/elements spec-args)))
              [[(get-type! context a path) (:ret transformed-spec)]])
             vec))
          []))
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

(defn get-spec-for-invoke
  "Return the spec for the thing being invoked at `[a path]`"
  [a path]
  (let [a* (get-in a path)
        v (get-in a (concat path [:fn :var]))]
    (or (when v
          (or (c/get-var-spec v)
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

(defn self-var-call?
  "True if the invoke at [a path] is a call to a var defined in a. Returns the path or nil"
  [a path]
  (let [a* (get-in a (conj path :fn))
        op (:op a*)]
    (when-let [v (:var a*)]
      (->> (a-def-paths a)
           (filter (fn [p]
                     (= v (get-in a (conj p :var)))))
           (first)))))

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
        _ (println "get-eq-invoke-spec:" (:form a*))
        s (get-spec-for-invoke a path)

        s-args (c/invoke-accept s)
        s-args (c/all-possible-values-length-n s-args (c/min-length s-args))]
    (assert s)
    (println "get-eq invoke spec" s)
    (->>
     (concat
      (map (fn [i s-a]
             (let [arg-path (conj path :args i)
                   arg-node (get-in a arg-path)
                   _ (assert arg-node)
                   t (get-type! context a arg-path)]
               (assert t)
               [t s-a])) (range (count (:args a*))) (c/elements s-args))
      (when (:ret s)
        (let [t (get-type! context a path)]
          [[t (:ret s)]])))
     (filterv identity))))

(defn get-eq-invoke-local-fn [context a path]
  {:post [(do (println "get-eq-invoke-local-fn:" (:form (get-in a path)) "=>" %) true)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (do
      (let [f (get-type! context a (conj path :fn))
            args-t (ensure-type! context a (conj path :args))
            ret-t (ensure-type! context a (conj path :ret))]
        [[f (c/fn-spec {:args args-t :ret ret-t})]
         [args-t (c/cat- (map-sequential-children get-type! context a path :args))]
         [t ret-t]]))))

(defmethod get-equations* :invoke [context a path]
  {:post [(do (println "get-eq invoke:" (:form (get-in a path)) "=>" %) true)
          (s/valid? ::equations %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (cond
      (invoke-local? a path) (get-eq-invoke-local-fn context a path)
      (self-var-call? a path) [[t (get-type! context a (conj (self-var-call? a path) :init))]]
      :else (get-eq-invoke-spec context a path))))

(defmethod get-equations* :if [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (if (get-in a (conj path :else))
      [[t (c/or- [(get-type! context a (conj path :then))
                  (get-type! context a (conj path :else))])]]
      [[t (get-type! context a (conj path :then))]])))

(defmethod get-equations* :throw [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/throw-form (get-type! context a (conj path :exception)))]]))

(defmethod get-equations* :new [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/class-spec (get-type! context a (conj path :class)))]]))

(defmethod get-equations* :recur [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO add equations that update loop bindings here
    [[t (c/recur-form (map-sequential-children get-type! context a path :exprs))]]))

(defmethod get-equations* :instance? [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO return value true/false when we know the check is true
    [[t (c/class-spec Boolean/TYPE)]]))

(defmethod get-equations* :vector [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/tuple-spec (map-sequential-children get-type! context a path :items))]]))

(defmethod get-equations* :loop [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (get-type! context a (conj path :body))]]))

(defmethod get-equations* :protocol-invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO verify arg count
    [[t (c/pred-spec #'any?)]
     [(get-type! context a (conj path :target)) (c/protocol- (-> a* :protocol))]]))

(defmethod get-equations* :keyword-invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO more specific, validate arg count
    [[t (c/pred-spec #'any?)]]))

(defmethod get-equations* :instance-field [context a path]
  {:post [(do (println "get-eq instance-field:" path "=>" %) true)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (f/get-java-field class field)]
    [[t (f/resolve-java-class-spec (:type f))]]))

(defmethod get-equations* :set [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    [[t (c/value (map-sequential-children get-type! context a path :items))]]))

(defn get-equations [context a]
  (walk-a-rec (fn [a path]
                (let [a* (get-in a path)
                      _ (assert a*)
                      {:keys [form op]} a*]
                  (->> (get-equations* context a path)
                       (mapv (fn [e]
                              (with-meta e {::form form
                                            ::op op})))))) a))

(defn resolve-type*
  [subst t]
  (let [resolve* (partial resolve-type* subst)]
    (loop [t t]
      (let [t* (get subst t t)]
        (cond
          (c/fn-spec? t*) (-> t*
                              (update-in [:args] resolve*)
                              (update-in [:args] (fn [args]
                                                   (if (c/cat? args)
                                                     (c/cat- (map (fn [a] (or (resolve* a) a)) (c/elements args)))
                                                     args)))
                              (update-in [:ret] resolve*))
          (c/or-spec? t*) (c/or- (map resolve* (c/elements t*)))
          (c/class-spec? t*) (-> t* (update-in [:cls] resolve*))
          (and (c/logic? t*) (not= t t*)) (recur t*)
          :else t*)))))

(defn resolve-type
  "Look up the type of t. If it maps to a type variable, recursively resolve"
  [subst t]
  (let [t* (resolve-type* subst t)]
    (if (not= t t*)
      (recur subst t*)
      t*)))

(s/fdef consolidate-equations :args (s/cat :eq ::equations) :ret ::equations)
(defn consolidate-equations [eqs]
  (->> eqs
       (group-by (fn [eq] (first eq)))
       (mapcat (fn [[l rs]]
                 (let [logic-rs (filter c/logic? (map second rs))
                       constraints (remove c/logic? (map second rs))]
                   (->>
                    (concat
                     (map (fn [rs]
                            [l rs]) logic-rs)
                     (when (seq constraints)
                       [[l (reduce c/add-constraint constraints)]]))
                    (filterv identity)))))))


(defn logic-n
  "If v is a logic variable, return its number, else nil"
  [v]
  (when (c/logic? v)
    (:name v)))

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
                  (let [subst* (u2/unify l r subst)]
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
                          (resolve-type subst t)
                          (c/invalid "inference failed" v))
                    v-s (if (and (c/or-spec? v-s)
                                 (every? c/fn-spec? (c/elements v-s)))
                          (c/merge-fn-specs (c/elements v-s))
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

(defn debug-equations [context eq]
  (let [type->forms (-> context :typenames deref vals (->> (map (fn [t] [t (-> t meta ::form)])) (into {})))]
    (doseq [e eq
            :let [[l r] e]]
      (println "[" l (-> l meta ::op) (type->forms l) (or (when (c/logic? r)
                                                        (type->forms r))
                                                      r) "]")
      ;; (println e (-> e meta))
      )))

(defn valid-subst?
  "True if everything conforms"
  [subst]
  (->> subst
       (vals)
       (every? c/conformy?)))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis :opts (s/? (s/keys :opt-un [::dependencies?]))) :ret (s/nilable c/spect?))
(defn infer [a & [{:keys [dependencies?]
                   :or {dependencies? true}}]]
  (let [context (new-context)]
    (when dependencies?
      (infer-dependencies a))
    (assign-typenames context a)
    (let [eq (apply concat (get-equations context a))
          _ (println "infer" (:form a))
          _ (println "infer" "eq1" eq)
          eq (consolidate-equations eq)
          eq (sort-equations eq)
          _ (println "infer" "eq2" eq)
          _ (debug-equations context eq)
          {:keys [subst fail]} (unify-all-equations eq)
          t (get-type! context a [])]
      (if fail
        (do
          (println "infer failed" (:form a) "fail:" fail subst)
          (debug-equations context eq))
        (if (valid-subst? subst)
          (do
            (store-var-inference-results context a subst)
            (resolve-type subst t)))))))

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
