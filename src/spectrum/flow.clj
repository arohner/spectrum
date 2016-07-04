(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec :as s]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.util :as util :refer (zip with-a unwrap-a)]))

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(s/def ::fn-spec (s/keys :req-un [::args ::ret ::fn]))
(s/def ::spec (s/or ::c/spect ::fn-spec))
(s/def ::var var?)

(s/def ::analysis (s/keys :req-un [:analyzer/op :analyzer/form]
                          :opt-un [::var ::spec]))

(s/def ::analysis? (s/nilable ::analysis))

(s/def ::analyses (s/coll-of ::analysis))

(s/fdef get-var-fn-spec :args (s/cat :v var?) :ret (s/nilable ::c/spect))

(defn get-var-fn-spec [v]
  (assert (var? v))
  (let [s (s/get-spec v)]
    (when s
      (c/parse-fn-spec s))))

(s/fdef flow-dispatch :args (s/cat :a ::analysis) :ret keyword?)
(defn flow-dispatch [a]
  (assert (:op a))
  (:op a))

(s/fdef flow :args (s/cat :a ::analysis) :ret ::analysis)

(defmulti flow
  "Given an analysis, walk and update-in the the analysis attaching ::specs and ::ret to values"
  #'flow-dispatch)

(s/fdef flow-ns :args (s/cat :as ::analyses) :ret ::analyses)

(defn flow-ns
  "Given the result of analyze-ns, flow all forms"
  [as]
  (map flow as))

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

(defn print-once* [& args]
  (apply println args))

(def print-once (memoize print-once*))

(defmethod flow :default [a]
  (print-once "TODO" "analyze op" (:op a))
  a)

(defmethod flow :def [a]
  (data/store-var-analysis a)
  (let [a (maybe-assoc-var-name a)]
    (if (-> a :init)
      (assoc a :init (flow (util/zip a :init)))
      a)))

(defmethod flow :with-meta [a]
  (update-in a [:expr] flow))

(defmethod flow :fn [a]
  (let [v (get a ::var)
        spec (when v
               (get-var-fn-spec v))
        a (if spec
            (assoc a ::spec spec)
            a)]
    (-> a
        (update-in [:methods] (fn [methods]
                                (mapv (fn [m]
                                        (flow (with-meta m {:a a}))) methods))))))

(defmethod flow :do [a]
  (-> a
      (update-in [:statements] (fn [statements] (mapv flow statements)))
      (update-in [:ret] flow)))

(defn object? [x]
  (instance? Object x))

(defn analysis->arg*-dispatch [x]
  (:op x))

(defmulti analysis->arg* #'analysis->arg*-dispatch)

(defmethod analysis->arg* :const [x]
  (-> x :val))

(s/fdef find-binding :args (s/cat :a ::analysis :name symbol?) :ret (s/nilable ::analysis))
(defn find-binding
  "recursively unwrap a, looking for a :binding for 'name"
  [a name]
  (or
   (condp = (:op a)
     :binding (->> a
                   :bindings
                   (filter (fn [b] (= name (:name b))))
                   first)
     :fn-method (->> a
                     :params
                     (filter (fn [b] (= name (:name b))))
                     first)
     nil
     ;; :local (print-once "TODO find-binding" :local)
     )

   (when-let [a* (unwrap-a a)]
     (recur a* name))))

(defmethod analysis->arg* :local [a]
  (let [b (find-binding a (:name a))]
    (or (::spec b) (c/unknown (:name a)))))

(s/fdef analysis->args :args (s/cat :a ::ana.jvm/analyses) :ret (s/coll-of ::c/spect))

(defn analysis->args
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/map->RegexCat {:ps (mapv (fn [arg]
                                (analysis->arg* (with-a arg args))) args)
                    :ret []}))

(def primitive->class {'long Long
                       'double Double})

(def class->primitive (set/map-invert primitive->class))

(defn primitive? [x]
  (contains? primitive->class x))

(defn long? [x]
  (instance? java.lang.Long))

(def class->pred {Long #'long?
                  Double #'double?
                  Integer #'int?
                  java.util.Date #'inst?
                  Number #'number?
                  Object #'object?})

(def pred->class (set/map-invert class->pred))

(s/def ::predicate fn?)

(s/fdef primitive->pred :args (s/cat :p primitive?) :ret class?)

(defn primitive->pred [p]
  (get class->pred (get primitive->class p)))

(s/def ::java-type (s/or :p primitive? :c class?))

(s/def ::java-args (s/coll-of ::java-type))

(s/fdef spec->java-args :args (s/cat :arg-spec ::c/spect) :ret ::java-args)
(defn spec->java-args
  "Given args spec, convert to java"
  [arg-spec]
  {:post [(every? identity %)]}
  (assert (instance? spectrum.conform.RegexCat arg-spec))
  (mapv (fn [arg]
          (spec->class arg)) (:ps arg-spec)))

(s/fdef resolve-class :args (s/cat :str symbol?) :ret class?)
(defn resolve-class
  [sym]
  (clojure.lang.RT/classForName (str sym)))

(s/fdef compatible-java-method? :args (s/cat :v ::java-args :m ::java-args) :ret boolean?)
(defn compatible-java-method?
  "True if values of type arg-a can be passed to a method that takes arg-b "
  [value-types method-types]
  (and
   (= (count value-types)
      (count method-types))
   (every? (fn [[v m]]
             (cond
               (primitive? m) (or (= m v) (= m (get class->primitive v)))
               (resolve-class m) (instance? (resolve-class m) v))) (map vector value-types method-types))))

(s/def ::reflect-name symbol?)
(s/def ::reflect-return-type ::java-type)
(s/def ::reflect-parameter-types ::java-args)

(s/def ::reflect-method (s/keys :req-un [::reflect-name ::reflect-return-type ::reflect-parameter-types]))

(s/fdef more-specific? :args (s/cat :v ::reflect-method :m ::reflect-method) :ret boolean?)
(defn more-specific?
  "Given two vectors of java args, return true if a is a more specific method than b"
  [a b]
  {:post [(do (println "more-specific?" a b "=>" %) true)]}
  (loop [[a & as] (:parameter-types a)
         [b & bs] (:parameter-types b)]
    (if (and a b)
      (cond
        (or (primitive? a) (contains? (parents a) (class b))) 1
        (or (primitive? b) (contains? (parents b) (class a))) -1
        :else (recur as bs))
      0)))

(s/fdef most-specific :args (s/cat :vecs (s/coll-of ::java-args)) :ret ::java-args)
(defn most-specific
  "Given a seq of vectors of java args, return the most specific method"
  [arg-vecs]
  (-> (sort more-specific? arg-vecs) last))

(s/fdef get-java-method :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret map?)
(defn get-java-method [cls method arg-spec]
  (->> (reflect/reflect cls)
       :members
       (filterv (fn [m]
                  (and (instance? clojure.reflect.Method m)
                       (= method (:name m)))))
       (filterv (fn [m]
                  (compatible-java-method? (spec->java-args arg-spec) (:parameter-types m))))
       (most-specific)))

(defn java-type->pred [t]
  {:post [(do (when-not %
                (println "java-type->pred:" t (class t) "=>" %)) true)]}
  (cond
    (primitive? t) (primitive->pred t)
    (symbol? t) (get class->pred (resolve-class t))
    (class? t) (get class->pred t)
    :else (assert "unknown type:" t)))

(s/fdef get-java-method-spec :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret ::fn-spec)
(defn get-java-method-spec
  "Return a fake spec for a java interop call"
  [cls method arg-spec]
  (let [m (get-java-method cls method arg-spec)
        _ (assert m)
        _ (println "method:" m)
        java-args (->> (mapv java-type->pred (:parameter-types m)))
        _ (println "java-args:" java-args)
        ret (c/parse-spec (java-type->pred (:return-type m)))]
    {:args (c/map->RegexCat {:ps (mapv c/parse-spec java-args)
                             :forms java-args
                             :ret []})
     :ret (c/parse-spec ret)}))

(defmethod flow :static-call [a]
  (println "static-call:" a)
  (let [cls (:class a)
        method (:method a)
        args (analysis->args (:args a))]
    (-> a
        (update-in [:args] (fn [args]
                             (mapv (fn [arg]
                                     (flow (with-meta arg {:a a}))) args)))
        (assoc ::spec (get-java-method-spec cls method args)))))

(defmethod flow :binding [a]
  ;;(println "flow binding:" a)
  a)

(declare assoc-form-spec)

(s/fdef get-invoke-fn-spec :args (s/cat :a ::analysis) :ret (s/nilable ::c/spect))

(defn get-invoke-fn-spec
  "Given an :fn a, return the spec"
  [a]
  ;;(println "get-invoke-fn-spec:" a)
  (when (-> a :op (= :var))
    (assert (var? (:var a))))

  (condp = (:op a)
    :var (get-var-fn-spec (:var a))))

(defn assoc-invoke-var [a]
  (let [v (-> a :fn :var)
        _ (assert v)
        s (get-var-fn-spec v)]
    (if s
      (assoc a ::spec s)
      a)))

;; (s/fdef get-form-spec :args (s/cat :a ::ana.jvm/analysis) :ret ::ana.jvm/analysis)
;; (defn get-form-spec
;;   "Given the :init of a binding, return the spec for the form, if any"
;;   [a]
;;   (or (::spec a) (assoc-form-spec a)))

(s/fdef assoc-spec-bindings :args (s/cat :a ::analysis) :ret ::analysis)
(defn assoc-spec-bindings
  "Given the :bindings from a let, assoc ::flow/spec to the binding, based on the right-hand value"
  [a]
  (-> a
      (update-in [:bindings] (fn [bindings]
                               (mapv (fn [b]
                                       (flow (with-meta b {:a a}))) bindings)))))

(defmethod flow :let [a]
  (-> a
      (assoc-spec-bindings)
      (update-in [:body] (fn [body]
                           (flow (with-meta body {:a a}))))))

(defn destructure-fn-params
  "Given a spect and ana.jvm/fn-method params, update params to include spec"
  [params spec]
  (loop [ret []
         params params
         spec spec]
    (if (seq params)
      (let [param (first params)
            s (c/first* spec)]
        (assert s)
        (if (:variadic? param)
          (conj ret (assoc param ::spec (c/rest* spec)))
          (recur (conj ret (assoc param ::spec s)) (rest params) (c/rest* spec))))
      ret)))

(defmethod flow :fn-method [a]
  (let [v (-> a meta :a ::var)
        s (if v
            (get-var-fn-spec v)
            (println "warning: no v:" a))
        a (if s
            (update-in a [:params] destructure-fn-params (:args s))
            (do
              (println "warning: no spec for " v)
              a))]
    (-> a
        (update-in [:body] (fn [body]
                             (flow (with-meta body {:a a})))))))
