(ns spectrum.flow
  (:require [clojure.core.memoize :as memo]
            [clojure.math.combinatorics :as combo]
            [clojure.data :refer [diff]]
            [clojure.java.io :as io]
            [clojure.pprint :refer [pprint]]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.string :as str]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.ann]
            [spectrum.analyzer :as analyzer]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.equations :as eq]
            [spectrum.java :as j]
            [spectrum.queue :as q]
            [spectrum.types :as t]
            [spectrum.util :as util :refer [print-once protocol? namespace? queue validate! instrument-ns memoize-with]])
  (:import [clojure.lang Var Namespace]))

(s/def ::a ::ana.jvm/analysis)

(s/def ::path-elem (s/or :k keyword? :i nat-int?))
(s/def ::path (s/coll-of ::path-elem :type vector?))

(s/def ::context (s/keys :req-un []))
(defn new-context []
  {:typenames (atom {})
   :shadow-types (atom {})})

(s/fdef a-loc :args (s/cat :a (s/nilable ::ana.jvm/analysis)) :ret (s/keys :opt-un [:ana.jvm.env/file :ana.jvm.env/line :ana.jvm.env/column]))
(defn a-loc [a]
  (select-keys a [:file :line :column]))

(defn a-loc-str
  "A human-formatted string for the file & line of the analysis"
  [a]
  (let [{{:keys [file line column]} :env} a]
    (str "file " file " line " line " col " column)))

(defn store-type! [context t a path]
  (let [a* (get-in a path)
        {:keys [form op]} a*
        t (with-meta t {::form form
                        ::op op
                        ::loc (a-loc a*)})]
    (-> context :typenames (swap! assoc [a path] t))))

(defn store-shadow-type!
  "Store that t-new is shadowing t-orig at and below path"
  [context t-orig t-new a path]

  (-> context :shadow-types (swap! update-in [t-orig] (fnil conj []) [path t-new])))

(defn subpath?
  "True if b is a path under a"
  [a b]
  (let [as a
        bs b]
    (loop [[a & ar] as
           [b & br] bs]
      (cond
        (and a b (= a b)) (recur ar br)
        (and b (nil? a)) true
        (and (nil? a) (nil? b)) true
        :else false))))

(s/fdef get-shadow-type :args (s/cat :c ::context :a ::a :p ::path :t ::t/type) :ret (s/nilable ::t/type))
(defn get-shadow-type
  "get the shadow type for original type t appearing at path, if any"
  [context a path t]
  (some->> context
           :shadow-types
           deref
           (#(get % t))
           (sort-by first)
           (map (fn [[shadow-path t]]
                  (when (subpath? shadow-path path)
                    t)))
           (filter identity)
           last))

(defn analyze-form
  "Analyze a form.

   (analyze-form '(string? 3))

   Optionally takes a map of keywordized variables to types:

   (analyze-form '(string? x) {:x #'string?})
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
                                            :atom (atom {::t (t/new-logic (name binding))})
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

(defn walk-a-rec-post
  "Given an analysis a, recursively call (f a path) on all of a's
  `:children`, post-ordered, and also `a` when `path` not provided. Return a seq of
  all `f` return values"
  ([f a]
   (let [path []]
     (concat
      (walk-a-rec-post f a path)
      [(f a [])])))
  ([f a path]
   (assert a)
   (assert (get-in a path))
   (mapcat (fn [c]
             (if (contains? (get-in a path) c)
               (let [new-path (conj path c)
                     c-node (get-in a new-path)]
                 (if (sequential? c-node)
                   (mapcat (fn [i]
                             (concat (walk-a-rec-post f a (conj new-path i)) [(f a (conj new-path i))])) (range (count c-node)))
                   (concat (walk-a-rec-post f a new-path) [(f a new-path)]))))) (get-in a (conj path :children)))))

(defn create-typename-dispatch [context a path]
  (:op (get-in a path)))

(defmulti create-typename #'create-typename-dispatch)

(defmethod create-typename :default [context a path]
  (store-type! context (t/new-logic) a path))

(defn binding-fn-method-analysis?
  "True if we have analysis for the :fn-method this :binding belongs to"
  [a path]
  {:post [(do (println "binding-fn-method-analysis?" path "=>" %) true)]}
  (-> (get-in a (-> path pop pop))
      :op
      (= :fn-method)))

(defmethod create-typename :binding [context a path]
  (let [t (t/new-logic (str "t"))
        a* (get-in a path)]
    (assert (:atom a*))
    (swap! (:atom a*) assoc ::t t ::path path)
    (store-type! context t a path)
    t))

(defmethod create-typename :local [context a path]
  nil)

(defmethod create-typename :fn [context a path]
  ;; we need an extra type on the :ret of a fn, in case it is called locally
  (let [fn-t (t/new-logic "t")
        ret-t (t/new-logic "t")
        a* (get-in a path)]
    (store-type! context fn-t a path)
    (store-type! context ret-t a (conj path :ret))
    fn-t))

(defmethod create-typename :fn-method [context a path]
  (let [fn-t (t/new-logic "t")
        ret-t (t/new-logic "t")
        a* (get-in a path)]
    (store-type! context fn-t a path)
    (store-type! context ret-t a (conj path :ret))
    fn-t))

(defn invoke-var-predicate?
  "if the expr at path is invoking a var predicate, return the var else nil"
  [a path]
  (let [a* (get-in a path)
        v (-> a* :fn :var)]
    (and (= :invoke (:op a*))
         v
         (c/var-pred? v)
         v)))

(defn assign-typenames
  "Walk the analysis, assign type names to every expression"
  [context a]
  (walk-a-rec-post (fn [a path]
                     (create-typename context a path)) a))

(defn get-equation-dispatch [context a path]
  (:op (get-in a path)))

(defmulti get-equation* #'get-equation-dispatch)

(defn get-type-dispatch [context a path]
  (-> a (get-in path) :op))

(defmulti get-type* #'get-type-dispatch)

(s/fdef get-type :ret (s/nilable ::t/type))
(defn get-type [context a path]
  (get-type* context a path))

(s/fdef with-form-meta :args (s/cat :c ::context :a ::ana.jvm/analysis :p ::path :eq ::eq/equation) :ret ::eq/equation)
(defn with-form-meta
  "add metatdata about the form the equation came from"
  [context a path e]
  (let [a* (get-in a path)
        t (get-type context a path)
        _ (assert (map? a*) path)
        {:keys [form op]} a*]
    (assert a*)
    (if (-> e meta (select-keys [::form ::op ::type]) seq)
      e
      (with-meta e (merge {::form form
                           ::op op
                           ::type t}
                          (a-loc a*))))))

(s/fdef get-equation :args (s/or :four (s/cat :c ::context :a ::a :p ::path :k (s/or :k keyword? :i int?))
                                  :three (s/cat :c ::context :a ::a :p ::path)
                                  :two (s/cat :c ::context :a ::a))
        :ret ::eq/equation)
(defn get-equation
  ([context a path]
   {:post [(validate! ::eq/equation % {:form (get-in a (conj path :form))})
           ;; (do (println "get-eq" (get-in a (conj path :form)) (get-in a (conj path :op)) %) true)
           ]}
   (println "get-eq" (get-in a (conj path :op)) (get-in a (conj path :form)))
   (->> (get-equation* context a path)
        (s/assert ::eq/equation)
        (with-form-meta context a path)))
  ([context a path key]
   (get-equation context a (conj path key)))
  ([context a]
   (get-equation context a [])))

(s/fdef get-equation-sequential :args (s/cat :c ::context :a ::a :bp ::path :k keyword?) :ret ::eq/equation)
(defn get-equation-sequential
  "Given a node with a sequential child, map get-equation over all children, and `and-e` together "
  [context a path key]
  (let [a* (get-in a (conj path key))]
    (assert (sequential? a*) path)
    (if (pos? (count a*))
      (eq/and-e
       (mapv (fn [i]
               (get-equation context a (conj path key) i)) (range (count a*))))
      (eq/true-e))))

(defmethod get-equation* :default [context a path]
  (let [a* (get-in a path)]
    (assert a*)
    (println "no equations for" (:form a*) (:op a*))
    (assert false))
  [])

(defn get-type-default [context a path]
  (-> context :typenames deref (get [a path])))

(defmethod get-type* :default [context a path]
  (get-type-default context a path))

(defmethod get-type* :local [context a path]
  {:pre [a (get-in a path)]
   :post [%]}
  (let [a* (get-in a path)
        t (-> a* :atom deref ::t)]
    (assert a*)
    (or (when t
          (get-shadow-type context a path t))
        t
        ;; workaround https://dev.clojure.org/jira/browse/TANAL-127
        (-> a* :env :locals (get (:name a*)) :atom deref ::t))))

(defn get-unshadowed-type [context a path]
  (let [a* (get-in a path)]
    (or (some-> a* :atom deref ::t)
        (get-type-default context a path)
        (some-> a* :env :locals (get (:name a*)) :atom deref ::t))))

(defn get-type-path
  "Given a type, return its path"
  [context t]
  {:post [%]}
  (->> context
       :typenames
       deref
       (filter (fn [[[a path] t*]]
                 (= t t*)))
       first
       first
       second))

(s/fdef get-type! :ret ::t/type)
(defn get-type! [context a path]
  {:post [(do (when-not %
                (println "get-type!" (:form a) (get-in a (conj path :op)) path "failed")) true)
          %]}
  (get-type* context a path))

(defmethod create-typename :if [context a path]
  (let [a* (get-in a path)
        if-t (store-type! context (t/new-logic) a path)]
    (when (invoke-var-predicate? a (conj path :test))
      (let [orig-t (get-type! context a (conj path :test :args 0))
            else? (boolean (get-in a (conj path :else)))
            then-t (t/new-logic orig-t)
            else-t (when else?
                     (t/new-logic orig-t))]
        (assert orig-t)
        ;; use the :then path for :tests, so (if (foo? x)) doesn't contaminate the :else branch
        (store-shadow-type! context orig-t then-t a (conj path :test))
        (store-shadow-type! context orig-t then-t a (conj path :then))
        (when else?
          (store-shadow-type! context orig-t else-t a (conj path :else)))))
    if-t))

(defn ensure-type!
  "Create or return the existing type at [a path]"
  [context a path]
  (if-let [t (get-type context a path)]
    t
    (let [t (t/new-logic (str "t"))]
      (store-type! context t a path)
      t)))

(defmethod get-equation* :binding [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (cond
      (::ret-spec a*) (eq/eq t (::ret-spec a*))
      (:init a*) (eq/and-e [(get-equation context a path :init)
                            (eq/eq t (get-type! context a (conj path :init)))])
      :else (eq/true-e))))

(def const-type-pred {:vector #'vector?
                      :map #'map?
                      :set #'set?})

(def const-type-dispatch :type)

(defmulti const-type
  "Given a :const node, return the spectrum type" #'const-type-dispatch)

(defmethod const-type :vector [a]
  (println "const-type vector" a)
  (println "const-type :vector a:" (t/or-t (map t/value-t (:val a))))

  (t/and-t [(if (seq (:val a))
              (t/vector-of (t/or-t (map t/value-t (:val a))))
              (t/and-t [(t/cat-t []) #'vector?]))
            (t/value-t (:val a))]))

(defmethod const-type :default [a]
  {:post [(do (println "const-type :default" (:form a) "=>" %) true)]}
  (t/canonicalize (t/value-t (:val a))))

(defmethod get-equation* :const [context a path]
  {:post [(do (println "get-eq :const" path "=>" %) true)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        tv-pred (get const-type-pred (:type a*))
        tv (const-type a*)]
    (eq/eq t tv)))

(defmethod get-equation* :def [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e [(eq/eq t #'var?)
               (when (get a* :init)
                 (get-equation context a path :init))])))

(defmethod get-equation* :do [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation-sequential context a path :statements)
      (get-equation context a path :ret)
      (eq/eq t (get-type! context a (conj path :ret)))])))

(defn map-sequential-children
  "Call `(f context a $path)` on each sequential child of (-> a (get-in path) key)"
  [f context a path key]
  (mapv (fn [i]
          (f context a (conj path key i))) (-> a (get-in (conj path key)) count range)))

(defmethod get-equation* :fn [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        fn-type (t/and-t (map-sequential-children get-type! context a path :methods))
        ret-types (map-sequential-children (fn [context a path]
                                            (get-type! context a (conj path :ret))) context a path :methods)]
    (eq/and-e
     [(get-equation-sequential context a path :methods)
      (eq/eq t fn-type)
      (eq/or-e (map (fn [ret-type]
                      (eq/<= ret-t ret-type)) ret-types))])))

(defn get-recur-paths
  "Given a node at `[a path]`, return paths to all `recur` nodes that recur to here"
  [a path]
  (let [a* (get-in a path)
        loop-id (:loop-id a*)]
    (assert loop-id)
    (->> (walk-a-rec (fn [a path]
                       (when (= loop-id (get-in a (conj path :loop-id)))
                         path)) a path)
         (filter identity))))

(defmethod get-equation* :fn-method [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ret-t (get-type! context a (conj path :ret))
        ret-type (get-type! context a (conj path :body))
        params (:params a*)
        variadic? (-> params last :variadic?)
        arg-ts (map-sequential-children get-type! context a path :params)
        recur-paths (get-recur-paths a path)
        recur-ts (map (fn [p]
                        (map-sequential-children get-type! context a p :exprs)) recur-paths)
        recur-args (when (seq recur-ts)
                     (apply map (fn [& args] (t/or-t args)) recur-ts))]
    (->>
     [(get-equation-sequential context a path :params)
      (get-equation context a path :body)
      (when variadic?
        (eq/eq (get-type! context a (conj path :params (dec (count params)))) (t/spec-t (t/seq-of (t/freshen '?x+)))))
      (eq/eq t (t/fn-t {arg-ts
                        ret-type}))
      (eq/eq ret-t ret-type)]
     (filter identity)
     (eq/and-e))))

(defmethod get-equation* :local [context a path]
  ;; workaround https://dev.clojure.org/jira/browse/TANAL-127
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (if-let [binding (-> a* :env :locals (get (:name a*)))]
      (do
        (println "get-eq local" binding)
        (assert (::ret-spec binding))
        (eq/eq t (::ret-spec binding)))
      (eq/true-e))))

(defmethod get-equation* :the-var [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/<= #'var? t)))

(defmethod get-equation* :quote [context a path]
  [])

(defmethod get-equation* :let [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation-sequential context a path :bindings)
      (get-equation context a path :body)
      (eq/eq t (get-type! context a (conj path :body)))])))

(defmethod get-equation* :try [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        body-t (get-type! context a (conj path :body))
        catches-t (map-sequential-children (fn [context a p]
                                             (get-type! context a p)) context a path :catches)
        finally-t (when (get-in a (conj path :finally))
                    (get-type! context a (conj path :finally)))
        ret-t (t/or-t (concat [body-t finally-t] catches-t))]
    (eq/and-e
     [(get-equation context a path :exception)
      (eq/eq t ret-t)])))

(defmethod get-equation* :catch [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        ex (get-in a (conj path :class :val))
        _ (assert (class? ex))
        ex-class-spec (t/class-t ex)]
    (eq/and-e
     [(get-equation context a path :class)
      (get-equation context a path :local)
      (get-equation context a path :body)
      (eq/eq t ex-class-spec)
      (eq/eq (get-type! context a (conj path :local)) ex-class-spec)])))

(defmethod get-equation* :map [context a path]
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
        _ (println "get-eq :map" ret-keys)
        ret-t (t/keys-t ret-keys)]
    (eq/and-e
     [(get-equation-sequential context a path :keys)
      (get-equation-sequential context a path :vals)
      (eq/eq t ret-t)])))

(defn resolve-java-class-spec [x]
  (t/class-t (j/resolve-java-class x)))

(defmethod get-equation* :static-field [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (j/get-java-field class field {:static? true})
        s (resolve-java-class-spec (:type f))]
    (assert s)
    (eq/eq t s)))

(defmethod get-equation* :with-meta [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e [(get-equation context a path :expr)
               (eq/eq t (get-type! context a (conj path :expr)))])))

(s/fdef method-class->t :args (s/cat :c class?) :ret ::t/type)
(defn method-class->t
  "Given an argument or return class from a java method, return a ::type"
  [c]
  (cond
    (j/primitive? c) (t/class-t c)
    (= c clojure.lang.ISeq) (t/seq-of #'any?)
    :else (t/or-t [(t/class-t c) #'nil?])))

(s/def :method/paramter-types (s/coll-of (s/or :c class? :n nil?)))
(s/def :method/return-types (s/or :c class? :n nil?))
(s/def ::method (s/keys :req-un [:method/parameter-types :method/return-type]))

(s/fdef method->fn-t :args (s/cat :m j/reflect-method?) :ret ::t/type)
(defn method->fn-t
  "Given a java method, translate it to a type, and add s/nilable to arguments & return type as necessary"
  [m]
  (let [{:keys [parameter-types declaring-class return-type name]} m
        declaring-class (j/resolve-java-class declaring-class)]
    (t/fn-t {(mapv (fn [param]
                     (-> param j/resolve-java-class method-class->t)) parameter-types)
             (-> return-type j/resolve-java-class method-class->t)})))

(s/fdef constructor->fn-t :args (s/cat :m j/reflect-constructor?) :ret ::t/type)
(defn constructor->fn-t
  "Given a java constructor, translate it to a type, and add s/nilable to arguments & return type as necessary"
  [m]
  (let [{:keys [parameter-types declaring-class name]} m
        declaring-class (j/resolve-java-class declaring-class)]
    (t/fn-t {(mapv (fn [param]
                     (-> param j/resolve-java-class method-class->t)) parameter-types)
             (t/class-t declaring-class)})))

(s/def ::eq-fn fn?)
(s/fdef make-equations :args (s/cat :a t/cat-t? :b t/cat-t? :opts (s/keys* :opt-un [::eq-fn])) :ret ::eq/equation)
(defn make-equations
  "Given two cats that should be `valid?`, zip each element together and return an equation"
  [a b & {:keys [eq-fn]
          :or {eq-fn eq/eq}}]
  {:post [(validate! ::eq/equation %)
          (do (println "make-equations:" a b "=>" %) true)]}
  (when-not (and (t/cat-t? a) (t/cat-t? b))
    (println "make-eq" a b))
  (assert (t/cat-t? a))
  (assert (t/cat-t? b))
  (eq/and-e
   (mapv (fn [ma ia]
           (eq-fn ma ia)) (t/cat-types a) (t/cat-types b))))

(defn analyze-cache-a [a]
  (walk-a-rec (fn [a path]
                (let [a* (get-in a path)]
                  (when (= :def (:op a*))
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

(s/fdef ensure-analysis :args (s/cat :ns namespace?))
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
          (let [v-t (c/get-var-type v)]
            (assert v-t (format "get-spec-for-invoke couldn't find spec for %s" v))
            (t/freshen v-t)))
        (assert false (format "get-spec-for-invoke couldn't find spec for %s %s" (:form a*))))))

(defn a-def-paths
  "Returns a seq of paths, one for each `:def` node in this analysis"
  [a]
  (->>
   (walk-a-rec (fn [a path]
                 (when (= :def (get-in a (conj path :op)))
                   path)) a)
   (filter identity)))

(defn self-var-reference?
  "True if the use of :var v at [a path] is a call to a var defined in a. Returns the path to the :def or nil"
  [a path]
  (let [a* (get-in a path)
        _ (assert (= :var (:op a*)))
        op (:op a*)]
    (when-let [v (:var a*)]
      (->> (a-def-paths a)
           (filter (fn [p]
                     (= v (get-in a (conj p :var)))))
           (first)))))

(defmethod get-type* :var [context a path]
  (or
   (when-let [new-path (some-> (self-var-reference? a path)
                               (conj :init))]
     (get-type* context a new-path))
   (get-type-default context a path)
   (assert false)))

(defmethod get-equation* :var [context a path]
  (let [a* (get-in a path)
        v (-> a* :var)
        t (get-type! context a path)]
    (if (self-var-reference? a path)
      (eq/true-e)
      (eq/eq t (t/freshen (c/get-var-type v))))))

(defn invoke-local?
  "Returns true if the invoke at [a path] is a local fn contained within a"
  [a path]
  (let [a* (get-in a (conj path :fn))
        op (:op a*)]
    (contains? #{:local :fn} op)))

(declare get-eq-invoke-fn-t)
(declare get-eq-invoke-t)

(s/fdef get-eq-invoke-logic :args (s/cat :f t/logic? :ia t/cat-t? :ret ::t/type) :ret ::eq/equation)
(defn get-eq-invoke-logic
  "Invoke on ?x"
  [f invoke-args ret-t]
  (let [ret (t/new-logic "ret")]
    (eq/eq f (t/fn-t {invoke-args ret-t}))))

(defn maybe-replace-invoke-t [invoke-args ret-t t]
  (if (t/invoke-t? t)
    (let [[f i-invoke-args] (t/type-values t)
          ret-eqs (get-eq-invoke-t f i-invoke-args ret-t)]
      ret-eqs)
    (eq/eq ret-t t)))

(s/fdef get-eq-invoke-fn-t :args (s/cat :f t/fn-t? :i ::t/type :r ::t/type) :ret ::eq/equation)
(defn get-eq-invoke-fn-t
  [f invoke-args ret-t]
  (let [fn-map (-> f (nth 1) t/fn-t t/type-value)
        ;; constraint that at least one arity must be successful
        req-one (->> fn-map
                     (map (fn [[f-args f-ret]]
                            (eq/<= f-args invoke-args)))
                     eq/or-e)
        ret-values (->> fn-map
                        (mapv (fn [[f-args f-ret]]
                                (->>
                                 (maybe-replace-invoke-t invoke-args ret-t f-ret)
                                 (eq/=> (eq/<= f-args invoke-args)))))
                        eq/or-e)]
    (eq/and-e [ret-values req-one])))

(s/fdef get-eq-thunk-invoke :args (s/cat :t t/invoke-t? :ret-t ::t/type) :ret ::eq/equation)
(defn get-eq-thunk-invoke [t ret-t]
  (let [[_ fn-t invoke-args] t]
    (get-eq-invoke-t fn-t invoke-args ret-t)))

(defn get-eq-invoke-ifn [t ret-t]
  (eq/eq ret-t #'any?))

(s/fdef get-eq-invoke-t :args (s/cat :t ::t/type :ia t/cat-t? :ret-t ::t/type) ::ret ::eq/equation)
(defn get-eq-invoke-t
  [t invoke-args ret-t]
  (cond
    (t/fn-t? t) (get-eq-invoke-fn-t t invoke-args ret-t)
    (t/logic? t) (get-eq-invoke-logic t invoke-args ret-t)
    (t/invoke-t? t) (get-eq-thunk-invoke t ret-t)
    :else (assert false (format "unknown invoke %s" t))))

(s/fdef get-eq-invoke-f :args (s/cat :c ::context :a ::a :p ::path) ::ret ::eq/equation)
(defn get-eq-invoke-f
  "get-equation for invoking something at `path`"
  [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        args (:args a*)
        invoke-args (t/cat-t (map-sequential-children get-type! context a path :args))
        f (get-type-for-invoke a path)
        ret-t (get-type! context a path)]
    (get-eq-invoke-t f invoke-args ret-t)))

(defn get-fn-method-with-arity
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

(defn get-eq-invoke-literal-fn
  "invoke of a fn literal, {:op :invoke {:op :fn}}"
  [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        f (get-type! context a (conj path :fn))
        invoke-args (t/cat-t (map-sequential-children get-type! context a path :args))
        method-path (get-fn-method-with-arity a (conj path :fn) (count (get-in a (conj path :args))))
        m (get-in a method-path)
        fn-args-t (t/cat-t (map-sequential-children get-type! context a method-path :params))
        ret-t (get-type! context a (conj path :fn :ret))]
    (assert f)
    (assert ret-t)
    (eq/and-e [(make-equations fn-args-t invoke-args :eq-fn eq/<=)
               (eq/eq ret-t t)])))

(s/fdef get-eq-invoke-local :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn get-eq-invoke-local
  "Invoke of a local variable {:op :invoke {:op :local}}"
  [context a path]
  {:post [(do (println "get-eq-invoke-local" %) true)
          (validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        f (get-type! context a (conj path :fn))
        f-path (get-type-path context f)
        invoke-args (map-sequential-children get-type! context a path :args)
        f-args (t/cat-t (mapv (fn [i]
                                (ensure-type! context a (conj f-path :args i) ;; {:variance :contravariant}
                                              )) (range (count invoke-args))))
        f-ret (ensure-type! context a (conj f-path :ret))]
    (assert f)
    (eq/and-e [(make-equations f-args (t/cat-t invoke-args) :eq-fn eq/<=)
               (eq/eq t f-ret)
               (eq/>= f (t/fn-t {f-args f-ret}))])))

(defn self-var-call?
  "True if the invoke at [a path] is a call to a var defined in a. Returns the path to the :def or nil"
  [a path]
  (self-var-reference? a (conj path :fn)))

(defn maybe-with-meta
  "Given a path, if [a path] is a :with-meta node, return the real path"
  [a path]
  (if (= :with-meta (get-in a (conj path :op)))
    (conj path :expr)
    path))

(defn get-eq-invoke-self-var [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [t (get-type! context a path)
        a* (get-in a path)
        var-path (self-var-call? a path)
        _ (assert var-path)
        fn-path (maybe-with-meta a (conj var-path :init))
        _ (assert fn-path)
        _ (assert (= :fn (:op (get-in a fn-path))))
        invoke-arg-count (count (:args a*))
        fn-method (get-fn-method-with-arity a fn-path invoke-arg-count)
        _ (assert fn-method)
        fn-method-ret (conj fn-method :ret)
        var-fn-ret-path (-> var-path (conj :init) (#(maybe-with-meta a %)) (conj :ret))]
    (eq/eq t (get-type! context a fn-method-ret))))

(defmethod get-equation* :invoke [context a path]
  (let [a* (get-in a path)
        t (get-type! context a path)
        invoke-op (get-in a* [:fn :op])]
    (eq/and-e
     [(get-equation-sequential context a path :args)
      (get-equation context a path :fn)
      (cond
        (= :fn invoke-op) (get-eq-invoke-literal-fn context a path)
        (= :local invoke-op) (get-eq-invoke-local context a path)
        (self-var-call? a path) (get-eq-invoke-self-var context a path)
        :else (get-eq-invoke-f context a path))])))

(defn get-method-t
  "Return a fn-t for the java method; includes all arity overloads"
  [cls method]
  ;; {:post [(do (println "get-method-t" cls method "=>" %) true)]}
  (or
   (some-> (data/get-ann [cls method])
           (t/freshen))
   (->> (j/get-java-method cls method)
        (mapv method->fn-t)
        (t/merge-fns))))

(s/fdef get-equation-java-call :ret ::eq/equation)
(defn get-equation-java-call [context a path]
  (let [a* (get-in a path)
        {:keys [class method instance]} a*]
    (if (and class method)
      (let [instance-type (when (:instance a*)
                            (get-type! context a (conj path :instance)))
            cls-class (:class a*)
            invoke-args (t/cat-t (map-sequential-children get-type! context a path :args))
            ret-t (get-type! context a path)
            method-t (get-method-t cls-class method)]
        (if method-t
          (let [ret-eq (->> [(get-equation-sequential context a path :args)
                             (when (get a* :instance)
                               (get-equation context a path :instance))
                             (get-eq-invoke-fn-t method-t invoke-args ret-t)
                             (when (and instance-type cls-class)
                               (eq/<= (t/class-t cls-class) instance-type))]
                            (filterv identity)
                            (eq/and-e))]
            (println "get-eq-java" (:form a*) method-t invoke-args ret-t  "=>" ret-eq)
            ret-eq)
          (assert false (format "no matching method: %s %s %s" class method instance))))
      (do
        (println "infer java call:" (:form a*) class method instance "unknown")
        (assert false)))))

(defmethod get-equation* :static-call [context a path]
  (get-equation-java-call context a path))

(defmethod get-equation* :instance-call [context a path]
  (get-equation-java-call context a path))

(defn invoke-equiv?
  "true if if the expression at path is a call to #'= or clojure.lang.Util/equiv"
  [a path]
  (let [a* (get-in a path)
        {cls :class method :method op :op} a*]
    (or (and (= :static-call op)
             (= clojure.lang.Util cls)
             (= 'equiv method))
        (and (= :invoke op)
             (= #'= (-> a* :fn :var))))))

(defn test-truthy?
  "true if the :if test expression is testing for a variable being truthy"
  [a path]
  (let [a* (get-in a path)]
    (and (= :local (:op a*)))))

(defn if-test-type
  "given the path to an :if test, return a keyword representing the kind of test"
  [context a path]
  (cond
    (invoke-var-predicate? a path) :predicate
    (invoke-equiv? a path) :equiv
    (test-truthy? a path) :truthy
    :else :unknown))

(s/fdef if-test-predicate-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-test-predicate-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  (let [v (invoke-var-predicate? a (conj path :test))
        arg-path (conj path :args 0)
        arg-t (get-type! context a arg-path)]
    (assert (var? v))
    (assert arg-t)
    [(eq/eq v arg-t)]))

(s/fdef if-test-equiv-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-test-equiv-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  (let [a* (get-in a path)
        arg-count (-> a* :test :args count)]
    (assert (:args a*))
    (->> arg-count
         dec
         (range)
         (map (fn [i]
                (let [l (get-type! context a (conj path :args i))
                      r (get-type! context a (conj path :args (inc i)))]
                  (eq/eq l r)))))))

(s/fdef if-test-truthy-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-test-truthy-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  (let [test* (get-in a (conj path :test))
        _ (assert (= :local (:op test*)))
        t (get-type! context a (conj path :test))]
    [(eq/eq (t/and-t [(t/not-t #'nil?) (t/not-t #'false?)]) t)]))

(s/fdef if-test-default-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-test-default-eqs [context a path]
  (let [t (get-type! context a (conj path :test))]
    [(eq/eq (t/and-t [(t/not-t #'nil?) (t/not-t #'false?)]) t)]))

(defn if-test-equation
  "Given the path to an :if test expression, return the equation that,
  if it unifies, the :then branch is taken"
  [context a path test-type]
  (condp =
      :predicate (if-test-predicate-eqs context a path)
      :equiv (if-test-equiv-eqs context a path)
      :truthy (if-test-truthy-eqs context a path)
      :unknown (if-test-default-eqs context a path)))

(s/fdef if-else-predicate-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-else-predicate-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  (let [v (invoke-var-predicate? a (conj path :test))
        arg-path (conj path :args 0)
        arg-t (get-type! context a arg-path)]
    (assert (var? v))
    (assert arg-t)
    [(eq/eq (t/not-t v) arg-t)]))

(s/fdef if-else-equiv-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-else-equiv-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  ;; TODO can we assert anything here?
  [])

(s/fdef if-else-truthy-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-else-truthy-eqs [context a path]
  (assert (= :if (:op (get-in a path))))
  (let [test* (get-in a (conj path :test))
        _ (assert (= :local (:op test*)))
        t (get-type! context a (conj path :test))]
    [(eq/eq (t/or-t [#'nil? #'false?]) t)]))

(s/fdef if-else-default-eqs :args (s/cat :c ::context :a ::a :p ::path) :ret ::eq/equation)
(defn if-else-default-eqs [context a path]
  (let [t (get-type! context a (conj path :test))]
    [(eq/eq (t/or-t [#'nil? #'false?]) t)]))

(defn if-else-equation
  "Given the path to an :if test expression, return the equation that,
  if it unifies, the :else branch is taken"
  [context a path test-type]
  (condp =
      :predicate (if-else-predicate-eqs context a path)
      :equiv (if-else-equiv-eqs context a path)
      :truthy (if-else-truthy-eqs context a path)
      :unknown (if-else-default-eqs context a path)))

(defmethod get-equation* :if [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        var-pred (invoke-var-predicate? a (conj path :test))
        else? (get-type context a (conj path :else))]
    (let [test-eqs (get-equation context a path :test)
          then-eqs (get-equation context a path :then)
          else-eqs (get-equation context a path :else)
          ;; TODO (eq/=> (eq/<= test-ret (value-t true)) (eq/eq ret-t then-t))
          ret-eq (if else?
                   (eq/or-e [(eq/eq t (get-type! context a (conj path :then))) (eq/eq t (get-type! context a (conj path :else)))])
                   (eq/or-e [(eq/eq t (get-type! context a (conj path :then))) (eq/eq t (t/value-t nil))]))]
      (eq/and-e [test-eqs then-eqs else-eqs ret-eq]))))

(defmethod get-equation* :throw [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation context a path :exception)
      (eq/eq t (t/throw-t (get-type! context a (conj path :exception))))])))

(defn get-constructor-t
  "Return an fn-t for this class constructor"
  [cls arity]
  {:post [(t/fresh-tagged? %)]}
  (t/freshen
   (or (data/get-ann cls)
       (->> (j/get-java-constructors cls arity)
            (map constructor->fn-t)
            (t/merge-fns)))))

(defmethod get-equation* :new [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        cls-t (get-type! context a (conj path :class))
        cls (-> a* :class :val)
        _ (assert (class? cls))
        invoke-args (t/cat-t (map-sequential-children get-type! context a path :args))
        constructor-fn-t (get-constructor-t cls (count (t/cat-types invoke-args)))]
    (println "constructor fn-t:" constructor-fn-t)
    (eq/and-e
     [(get-equation-sequential context a path :args)
      (get-equation context a path :class)
      (get-eq-invoke-fn-t constructor-fn-t invoke-args t)])))

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

(defmethod get-equation* :recur [context a path]
  {:post [(validate! ::eq/equation %)]}
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
      (get-equation-sequential context a path :exprs)
      (eq/false-e (print-str "mismatch recur args:" (count recur-args) "vs." (count dest-args))))))

(defmethod get-equation* :instance? [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO return value true/false when we know the check is true
    (eq/and-e [(get-equation context a path :target)
               (eq/eq t (t/class-t Boolean/TYPE))])))

(defmethod get-equation* :vector [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation-sequential context a path :items)
      (eq/eq t (t/and-t [(t/cat-t (map-sequential-children get-type! context a path :items))
                         (t/vector-of (c/value-coll-type (map-sequential-children get-type! context a path :items)))]))])))

(defmethod get-equation* :loop [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation-sequential context a path :bindings)
      (get-equation context a path :body)
      (eq/eq t (get-type! context a (conj path :body)))])))

(defmethod get-equation* :protocol-invoke [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO verify arg count
    (eq/and-e
     [(get-equation context a path :target)
      (get-equation context a path :protocol-fn)
      (get-equation context a path :args)
      (eq/eq t #'any?)
      (eq/eq (get-type! context a (conj path :target)) (t/protocol-t (-> a* :protocol)))])))

(defmethod get-equation* :keyword-invoke [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    ;; TODO more specific, validate arg count
    (eq/and-e
     [(get-equation context a path :keyword)
      (get-equation context a path :target)
      (eq/eq t #'any?)])))

(defmethod get-equation* :instance-field [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)
        {:keys [field class]} a*
        f (j/get-java-field class field)]
    (eq/and-e
     [(get-equation context a path :instance)
      (eq/eq t (resolve-java-class-spec (:type f)))])))

(defmethod get-equation* :set [context a path]
  {:post [(validate! ::eq/equation %)]}
  (let [a* (get-in a path)
        t (get-type! context a path)]
    (eq/and-e
     [(get-equation-sequential context a path :set)
      (eq/eq t (t/value-t (map-sequential-children get-type! context a path :items)))])))

(defmethod get-equation* :host-interop [context a path]
  {:post [(validate! ::eq/equation %)]}
  (get-equation context path :target))

(s/def :state/fail (s/nilable ::eq/equation))
(s/def ::unify-state (s/keys :req-un [:state/fail ::c/substs]))

(defn logic-n
  "If v is a logic variable, return its number, else nil"
  [v]
  (when (t/logic? v)
    (let [[_ n] (re-find #"(\d+)$" (name v))]
      (Long/parseLong n))))

(defn unify-eq-dispatch [state e]
  (first e))

(defmulti unify-equation #'unify-eq-dispatch)

(defmethod unify-equation :eq [{:keys [substs fail] :as state} eq]
  (if fail
    state
    (let [[_ l r] eq]
      (let [substs* (seq (c/unify l r substs))]
        (if substs*
          (assoc state :substs substs*)
          (assoc state :fail eq))))))

(defmethod unify-equation :conde! [{:keys [substs fail] :as state} eq]
  (if fail
    state
    (let [pairs (-> eq
                    (nth 1)
                    t/sort-ts)
          states (->> pairs
                      (map (fn [[test then]]
                             (validate! ::eq/equation test)
                             (validate! ::eq/equation then)
                             (let [state (unify-equation state test)]
                               (if (not (:fail state))
                                 (do
                                   ;; (println "conde:" test "matched")
                                   (unify-equation state then))
                                 (do
                                   ;; (println "conde" test "failed")
                                   nil)))))
                      (doall))]
      (or
       (when (every? nil? states)
         (assoc state :fail eq))
       (->> states
            (filter :fail)
            first)
       (when (->> states
                  (remove :fail)
                  seq
                  nil?)
         (assoc state :fail eq))
       (do
         (assert (nil? (seq (filter :fail states))))
         (assert (some :substs states))
         (->> states
              (remove :fail)
              (mapcat :substs)
              ((fn [substs]
                 (assoc state :substs substs)))))))))

(s/def ::fail (s/nilable ::eq/equation))
(s/def :empty/substs (s/nilable (s/coll-of ::c/subst :kind sequential? :min-count 0)))
(s/def :non-empty/substs (s/coll-of ::c/subst :kind sequential? :min-count 1))
(s/def ::state (s/keys :req-un [(or :non-empty/substs (and :empty/substs ::fail))]))

(defn new-state []
  {:substs [{}] :fail nil :i 0})

(defn simplify-eq-dispatch [e]
  (nth e 0))

(defmulti simplify-equation #'simplify-eq-dispatch)

(defmethod simplify-equation :ande [e]
  (eq/and-e (mapv simplify-equation (eq/get-eqs e))))

(defmethod simplify-equation :ore [e]
  {:post [(do (println "simplify ore:" e "=>" %) true)]}
  (eq/or-e (mapv simplify-equation (eq/get-eqs e))))

(defmethod simplify-equation :imp [e]
  {:post [(do (println "simplify imp:" e "=>" %) true)]}
  (let [[_ test then] e]
    (eq/=> (simplify-equation test) (simplify-equation then))))

(defn simplify-1 [x y]
  (or
   (when (or (t/invalid? x) (t/invalid? y))
     (eq/false-e))
   (when (and (nil? x) (nil? y))
     (eq/true-e))
   (when (and (nil? x) (c/accept-nil? y))
     (eq/true-e))
   (when (and (c/accept-nil? x) (nil? y))
     (eq/true-e))
   (when (and (nil? x) (not (c/accept-nil? y)))
     (eq/false-e))
   (when (and (not (c/accept-nil? x)) (nil? y))
     (eq/false-e))))

(s/fdef simplify-regex :args (s/cat :eqf ifn? :x any? :y any?) :ret ::eq/equation)
(defn simplify-regex [eq-f x y]
  {:post [(do (println "simplify-re" x y "=>" %) true)]}
  (or
   (simplify-1 x y)
   (->> (combo/cartesian-product (c/re-will-accept x) (c/first-t y))
        (map (fn [[xv yv]]
               (assert xv)
               (assert yv)
               (let [new-x (c/re-accept x yv)
                     new-y (c/re-accept y yv)]
                 (println "new-x" new-x)
                 (println "new-y" new-y)
                 (->> (combo/cartesian-product new-x new-y)
                      (map (fn [[new-x* new-y*]]
                             (eq/and-e [(eq-f xv yv)
                                        (simplify-regex eq-f new-x* new-y*)])))
                      (eq/or-e)))))
        (eq/or-e))))

(defmethod simplify-equation :eq [e]
  (let [[_ x y] e]
    (if (and (t/regex? x) (t/regex? y))
      (simplify-regex eq/eq x y)
      e)))

(defmethod simplify-equation :<= [e]
  (let [[_ x y] e]
    (if (and (t/regex? x) (t/regex? y))
      (simplify-regex eq/<= x y)
      e)))

(defmethod simplify-equation :>= [e]
  (let [[_ x y] e]
    (if (and (t/regex? x) (t/regex? y))
      (simplify-regex eq/>= x y)
      e)))

(defn solve-eq-dispatch [substs e]
  (nth e 0))
(defmulti solve-equation* #'solve-eq-dispatch)

(defn sort-eqs
  "Given a seq of eqs, sort them in a way that minimizes work"
  [eqs]
  ;; move the :ors to the end
  (sort-by (fn [e]
             (condp = (eq/eq-tag e)
               :true 0
               :false 0
               :ore 2
               1)) eqs))

(defmethod solve-equation* :ande [state e]
  {:post [;; (do (when (:fail %) (println "solve failed:" e)) true)
          (validate! ::state %)]}
  (let [eqs (-> e (eq/get-eqs) (sort-eqs))]
    (reduce
     (fn [state e*]
       (if (not (:fail state))
         (let [substs-old (:substs state)
               {:keys [substs] :as state} (solve-equation* state e*)
               state (update-in state [:i] inc)]
           ;; (println "solve eq" e* "=>" (not (:fail state)))
           (if (not (:fail state))
             (if (= :ore (eq/eq-tag e))
               (update-in state [:substs] concat substs)
               (assoc state :substs substs))
             state))
         state)) state eqs)))

(defmethod solve-equation* :ore [state e]
  {:post [;; (do (println "solve :ore" e "=>" (not (:fail %))) true)
          (validate! ::state %)]}
  (let [states (->> (nth e 1)
                    (sort-eqs)
                    (map (fn [e*]
                           {:post [;; (do (println "solve eq" e* "=>" (not (:fail %))) true)
                                   ]}
                           (solve-equation* state e*)))
                    (doall))
        failed (filter :fail states)
        successful (remove :fail states)]
    ;; (println "solve :ore:" states)
    (if (seq successful)
      (->> states (remove :fail) (mapcat :substs) ((fn [substs] (assoc state :substs substs))))
      (assoc state :fail e))))

(defmethod solve-equation* :imp [state e]
  {:post [;; (do (when (:fail %) (println "solve failed:" e)) true)
          (validate! ::state %)]}
  (let [[_ test then] e
        state-orig state
        state (solve-equation* state test)]
    (if (not (:fail state))
      (solve-equation* state then)
      state-orig)))

(defmethod solve-equation* :true [state e]
  {:post [(validate! ::state %)]}
  state)

(defmethod solve-equation* :false [state e]
  {:post [(validate! ::state %)]}
  (assoc state :fail e))

(defmethod solve-equation* :eq [state e]
  {:post [(validate! ::state %)]}
  (if (not (:fail state))
    (if-let [substs (c/unify (nth e 1) (nth e 2) (:substs state))]
      (assoc state :substs substs)
      (assoc state :fail e))
    state))

(defmethod solve-equation* :<= [state e]
  {:post [(do (when (:fail %) (println "solve failed:" e)) true)
          (validate! ::state %)]}
  (let [[_ x y] e]
    (if (not (:fail state))
      (let [substs (or (c/unify x y (:substs state))
                       (do
                         (println "narrow attempt:" x y )
                         (c/narrow-unify x y (:substs state))))]
        ;; (do (println "solve <=" x y "=>" (boolean (seq substs))))
        (if substs
          (assoc state :substs substs)
          (assoc state :fail e)))
      state)))

(defmethod solve-equation* :>= [state e]
  {:post [(do (when (:fail %) (println "solve failed:" e)) true)
          (validate! ::state %)]}
  (let [[_ x y] e]
    (if (not (:fail state))
      (let [substs (or (c/unify x y (:substs state))
                       (do
                         (println "solve >=" e "widening")
                         (c/unify (t/or-t [x y]) y (:substs state))))]
        (println "solve >=" x y "=>" (boolean (seq substs)))
        (if (seq substs)
          (assoc state :substs substs)
          (assoc state :fail e)))
      state)))

(defn solve [e]
  (println "solve:")
  (pprint e)
  (->> e
       (simplify-equation)
       (solve-equation* (new-state))))

(s/fdef unify-all-equations :args (s/cat :eqs ::eq/equation) :ret ::unify-state)
(defn unify-all-equations [e]
  ;; important to keep ordering here. Weird. Why is order important?
  (let [state {:substs [{}] :fail nil :i 0}]
    (->> e
         (reduce (fn [state eq]
                   (println "unify-all eq" (:i state) eq)
                   (def state state)
                   (def eq eq)
                   (let [substs-old (:substs state)
                         {:keys [substs] :as state} (unify-equation state eq)
                         state (update-in state [:i] inc)]
                     (if (not (:fail state))
                       (assoc state :substs substs)
                       state))) state))))

(defn get-var-types
  "Return the (unresolved) types that correspond to var :inits in analysis"
  [context a]
  (->> (a-def-paths a)
       (map (fn [def-p]
              (let [var-a (get-in a def-p)
                    v (get-in a (conj def-p :var))
                    init-p (conj def-p :init)
                    t (get-type! context a init-p)]
                [v t])))
       (into {})))

(defn store-var-inference-results [context a substs]
  (->> (a-def-paths a)
       (map (fn [def-p]
              (let [var-a (get-in a def-p)
                    v (get-in a (conj def-p :var))
                    init-p (conj def-p :init)
                    t (get-type! context a init-p)
                    _ (println "resolving" t)
                    v-s (c/resolve-type t substs)]
                (assert v-s)
                (println "storing" t v v-s)
                (data/store-var-spec v v-s)
                [v v-s])))
       (into {})))

(s/fdef a-vars :args (s/cat :v ::ana.jvm/analysis) :ret (s/coll-of var? :kind set?))
(defn a-vars
  "Return all vars referenced in this analysis"
  [a]
  (->> a
       (walk-a-rec (fn [a path]
                     (:var (get-in a path))))
       (filter identity)
       (set)))

(s/fdef var-dependencies :args (s/cat :v var?) :ret (s/coll-of var? :kind set?))
(defn var-dependencies
  "Return all vars this var depends on. Analyzes if necessary"
  [v]
  (ensure-analysis-var v)
  (let [{:keys [a]} (data/get-var-analysis v)]
    (if a
      (-> a a-vars (disj v))
      #{})))

(s/def :var-dependencies/map (s/map-of var? (s/coll-of var?)))

(s/fdef dependencies-map :args (s/cat :vs (s/coll-of var?)) :ret :var-dependencies/map)
(defn dependencies-map
  "Return a map of vars this var depends on"
  [v]
  (loop [dep-map {}
         queue (q/q v)]
    (if-let [v (first queue)]
      (let [deps (var-dependencies v)
            seen (set (keys dep-map))
            new (set/difference deps seen)]
        (recur (assoc dep-map v deps) (pop (apply conj queue new))))
      dep-map)))

(s/fdef a-var-dependencies :args (s/cat :a ::a) :ret :var-dependencies/map)
(defn a-var-dependencies
  "Given an analysis, return a dependency map of all vars the analysis depends on"
  [a]
  (-> a
      (a-vars)
      (dependencies-map)))

(declare infer)

(s/def ::dependencies? (s/nilable boolean?))

(s/fdef infer-var :args (s/cat :v var? :opts (s/? (s/keys :opt-un [::dependencies?]))))
(defn infer-var [v & [{:keys [dependencies?]
                       :or {dependencies? true}}]]
  (ensure-analysis-var v)
  (if-let [{:keys [a]} (data/get-var-analysis v)]
    (let [t (infer a {:dependencies? dependencies?})]
      t)
    (println "couldn't find analysis for" v)))

(defn infer-cycle
  "Given a seq of vars that form a cycle, infer them together"
  [vs]
  (doseq [v vs]
    (ensure-analysis-var v))
  (let [as {:op :do
            :statements (mapv (fn [v]
                                {:post [%]}
                                (data/get-var-analysis v)) vs)
            :ret {:op :const
                  :val nil}}]
    (infer as)))

(defn ensure-infer-var-cycle [vs]
  (if (every? c/get-var-type vs)
    nil
    (infer-cycle vs)))

(defn ensure-infer-var [v &[{:keys [dependencies?]}]]
  (or (c/get-var-type v)
      (do
        (println "inferring var" v)
        (infer-var v {:dependencies? dependencies?}))))

(defn sort-dependencies
  "Given a var dependency map, return a seq of vars to visit in
  order. Returns collections of vars to represent cycles"
  [dm]
  (loop [nodes (set/union (set (keys dm)) (set (apply concat (vals dm))))
         returned #{}
         ret []]
    (if-let [n (first nodes)]
      (let [visit (fn visit
                    ([n stack visiting]
                     {:pre [(var? n)]}
                     (let [deps (get dm n)
                           to-visit (remove (fn [d]
                                              (contains? returned d)) deps)
                           can-ret? (nil? (seq to-visit))]
                       (cond
                         (and (contains? returned n) (seq stack)) (recur (peek stack) (pop stack) visiting)
                         (some #(= n %) visiting) (let [cycle (drop-while #(not= n %) visiting)]
                                                    (println "not a dag:" n cycle)
                                                    cycle)
                         (seq to-visit) (recur (first to-visit) (into stack to-visit) (conj visiting n))
                         :else n)))
                    ([n]
                     (visit n (list) [])))]
        (let [new-ret (visit n)]
          (if (coll? new-ret)
            (recur (apply disj nodes new-ret) (into returned new-ret) (conj ret new-ret))
            (recur (disj nodes new-ret) (conj returned new-ret) (conj ret new-ret)))))
      ret)))

(defn infer-dependencies
  "Infer all var dependencies contained in analysis a"
  [a]
  (->> a
       (a-var-dependencies)
       (sort-dependencies)
       (map (fn [v]
              {:post [(do (when-not % (println "failed to infer" v)) true)
                      %]}
              (if (coll? v)
                (ensure-infer-var-cycle v)
                (ensure-infer-var v {:dependencies? false}))))
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

(defn debug-form-eqs
  "Print each form, and its associated equations"
  [context eqs]
  (let [get-type-eqs (fn
                       [t]
                       "return all equations associated with the form for this type"
                       (->> eqs
                            (filterv (fn [eq]
                                       (-> eq meta ::type (= t))))))]
    (->> @(:typenames context)
         set/map-invert
         (sort-by (fn [[t _]]
                    (logic-n t)))
         (map (fn [[t [a path]]]
                (when-let [eqs (seq (get-type-eqs t))]
                  (println (get-in a (conj path :op)) (get-in a (conj path :form)) eqs)
                  (println ""))))
         (dorun))))

(defn debug-all-types [context]
  (println "debug-all-types")
  (->> context
       :typenames
       deref
       set/map-invert
       (sort-by (fn [[t _]]
                  (logic-n t)))
       (map (fn [[t [a path]]]
              (println t (get-in a (conj path :op)) (or (get-in a (conj path :form)) path))))
       (dorun))
  (when (->> context
             :shadow-types
             deref
             (seq))
    (println "shadow types:")
    (->> context
         :shadow-types
         deref
         (sort-by (fn [[t _]]
                    (logic-n t)))
         (map (fn [[t-orig shadows]]
                (->> shadows
                     (map (fn [[path t-new]]
                            (println t-orig path "=>" t-new)))
                     (dorun))))
         (dorun))))

(defn debug-failed-eq-dispatch [context eq subst]
  {:post [(keyword? %)]}
  (nth eq 0))

(defmulti debug-failed-eq #'debug-failed-eq-dispatch)

(defn debug-failed-equation [context eq subst]
  (let [[eq-op l r] eq
        l-meta (get-type-meta context l)
        existing-l (c/resolve-type l subst)
        existing-r (c/resolve-type r subst)]
    (println "expected" l (if-let [form (::form l-meta)] form "") "=>" (c/resolve-type r subst))

    (when existing-l
      (println "could not unify eq" eq (if-let [form (::form l-meta)] form "") "at" (::loc l-meta) "with existing l:" existing-l "existing-r:" r "->" existing-r "subst:" subst)
      (prn "form:" l r [subst]))

    (doseq [lv (t/get-lvars eq)]
      (println lv "=>" (c/resolve-type lv subst)))
    (doseq [lv (t/get-lvars existing-l)]
      (println lv "=>" (c/resolve-type lv subst)))))

(defmethod debug-failed-eq :eq [context eq subst]
  (debug-failed-equation context eq subst))

(defmethod debug-failed-eq :ore [context eq subst]
  (let [[eq-op eqs] eq]
    (println eq "failed")
    (println "could not unify any of" eqs)

    (doseq [e eqs]
      (debug-failed-eq context e subst))))

(defmethod debug-failed-eq :ande [context eq subst]
  (let [[eq-op eqs] eq]
    (println eq "failed")
    (println "could not unify one of" eqs)

    (doseq [e eqs]
      (debug-failed-eq context e subst))))

(defmethod debug-failed-eq :<= [context eq subst]
  (println "could not solve" eq))

(defmethod debug-failed-eq :false [context eq subst]
  (println "could not solve" eq))

(defn debug-failure
  "Given a unify failure, print relevant debugging"
  [context a eqs subst fail]
  (debug-all-types context)
  (debug-form-eqs context eqs)

  (println "infer failed" (:form a) "failing equation:" fail)
  (debug-failed-eq context fail subst)
  (println "fail" fail " meta:" (-> fail meta))
  ;; (println "subst" subst)
  )

(defn valid-subst?
  "True if everything conforms"
  [subst]
  (->> subst
       (vals)
       (every? t/conformy?)))

(s/fdef infer :args (s/cat :a ::ana.jvm/analysis :opts (s/? (s/keys :opt-un [::dependencies?]))) :ret (s/nilable ::t/type))
(defn infer [a & [{:keys [dependencies?]
                   :or {dependencies? true}}]]
  {:post [(do (println "infer:" (:form a) "=>" %) true)]}
  (let [context (new-context)]
    (when dependencies?
      (infer-dependencies a))
    (assign-typenames context a)
    (debug-all-types context)

    (let [e (get-equation context a)
          _ (println "equation:")
          _ (pprint e)
          t (get-type! context a [])
          _ (def e e)
          _ (def t t)
          _ (def context context)
          _ (def var-types (get-var-types context a))
          _ (println "solving for " (or (seq (get-var-types context a)) t))
          {:keys [substs fail]} (solve e)
          _ (println "infer" "done unifying" (count substs) (count (distinct substs)))]
      (def substs substs)
      (debug-form-eqs context e)
      (pprint e)
      (if fail
        (debug-failure context a e substs fail)
        (when substs
          ;; (println substs)
          (let [type-map (store-var-inference-results context a substs)]
            (println (keys type-map))
            (or (some-> type-map first val)
                (c/resolve-type t substs))))))))

(defn infer-form
  ([form]
   (println "infer-form:" form)
   (-> form
       (analyze-form)
       infer))
  ([form specs]
   (-> form
       (analyze-form specs)
       infer)))

(instrument-ns)
