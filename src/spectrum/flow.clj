(ns spectrum.flow
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.reflect :as reflect]
            [clojure.set :as set]
            [clojure.spec :as s]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.data :as data]
            [spectrum.java :as j]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)]))

(def empty-fn-spec {:args nil, :ret nil, :fn nil})

(s/def ::args ::c/spect)
(s/def ::ret ::c/spect)
(s/def ::fn (s/nilable ::c/spect))

(s/def ::fn-spec (s/keys :req-un [::args ::ret ::fn]))
(s/def ::spec (s/or ::c/spect ::fn-spec))
(s/def ::args-spec ::spec)
(s/def ::ret-spec ::spec)
(s/def ::var var?)

(s/def ::analysis (s/keys :req []
                          :req-un [::ana.jvm/op ::ana.jvm/form]
                          :opt [::var ::args-spec ::ret-spec]))

(s/def ::analysis? (s/nilable ::analysis))

(s/def ::analyses (s/coll-of ::analysis))

(s/fdef get-var-fn-spec :args (s/cat :v var?) :ret (s/nilable ::c/spect))

(defn a-loc [a]
  (select-keys a [:file :line :column]))

(defn a-loc-str
  "A human-formatted string for the file & line of the current analysis"
  [a]
  (let [{{:keys [file line column]} :env} a]
    (str "file " file " line " line " col " column)))

(s/fdef flow-dispatch :args (s/cat :a ::analysis) :ret keyword?)
(defn flow-dispatch [a]
  (assert (:op a))
  (:op a))

(s/fdef flow :args (s/cat :a ::analysis) :ret ::analysis)

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

(defmethod flow :default [a]
  (println "TODO" "flow op" (:op a))
  a)

(defmethod flow :quote [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:expr] (fn [expr]
                                 (flow (with-a expr a))))]
    (assoc a ::ret-spec (-> a :expr ::ret-spec))))

(defmethod flow :def [a]
  {:post [(::ret-spec %)]}
  (data/store-var-analysis a)
  (let [a (maybe-assoc-var-name a)
        a (update-in a [:init] (fn [i]
                                 (when i
                                   (flow (with-a i a)))))]
    (assoc a ::ret-spec (c/parse-spec #'var?))))

(defmethod flow :the-var [a]
  {:post [(::ret-spec %)]}
  ;; the-var => (var foo). Returns the actual var
  (assoc a ::ret-spec (c/parse-spec #'var?)))

(defmethod flow :var [a]
  {:post [(::ret-spec %)]}
  ;; :var => the value the var holds
  (assoc a ::ret-spec (c/value @(:var a))))

(defmethod flow :with-meta [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:expr] (fn [e]
                                 (flow (with-a e a))))]
    (assoc a ::ret-spec (::ret-spec (:expr a)))))

(defmethod flow :fn [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:methods] (fn [methods]
                                    (mapv (fn [m]
                                            (flow (with-a m a))) methods)))]
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

(defmethod find-binding* :fn-method [a name]
  (->> a
       :params
       (filter (fn [b] (= name (:name b))))
       first))

(s/fdef find-binding :args (s/cat :a ::analysis :name symbol?) :ret (s/nilable ::analysis))
(defn find-binding
  "recursively unwrap a, looking for a :binding for 'name"
  [a name]
  (if-let [b (find-binding* a name)]
    b
    (when-let [a* (unwrap-a a)]
      (recur a* name))))

(s/fdef analysis-args->spec :args (s/cat :a ::analyses) :ret (s/coll-of ::c/spect))

(defn analysis-args->spec
  "Given the analysis of a fn invoke, return the args for a compatible c/conforms? call"
  [args]
  (c/map->RegexCat {:ps (mapv (fn [arg]
                                (assert (::ret-spec arg))
                                (::ret-spec arg)) args)
                    :ret []}))

(defn get-var-fn-spec [v]
  (c/parse-spec (s/get-spec v)))

(defmethod flow :invoke [a]
  {:post [(::ret-spec %)]}
  (let [v (-> a :fn :var)
        spec (when v
               (get-var-fn-spec v))
        a (update-in a [:args] (fn [args]
                                 (mapv (fn [arg]
                                         (flow (with-a arg a))) args)))
        spec (when spec
               (c/maybe-transform v spec (analysis-args->spec (:args a))))]
    (if v
      (if spec
        (if (:ret spec)
          (assoc a ::ret-spec (:ret spec))
          (do
            (print-once "warning: no ret-spec for" (:var (:fn a)))
            (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))
        (do
          (print-once "warning: no spec for" (:var (:fn a)))
          (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))
      (do
        (print-once "warning: invoke non-var unknown:" (:form (:fn a)) (a-loc-str a))
        (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))))

(defmethod flow :protocol-invoke [a]
  {:post [(::ret-spec %)]}
  (let [v (-> a :fn :var)
        spec (when v
               (get-var-fn-spec v))
        a (update-in a [:target] (fn [t]
                                   (flow (with-a t a))))
        a (update-in a [:args] (fn [args]
                                 (mapv (fn [arg]
                                         (flow (with-a arg a))) args)))
        spec (when spec
               (c/maybe-transform v spec (analysis-args->spec (:args a))))]
    (if v
      (if spec
        (assoc a ::ret-spec (:ret spec))
        (do
          (print-once "warning: no spec for" (:var (:fn a)))
          (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))
      (do
        (print-once "warning: invoke non-var unknown:" (:form (:fn a)) (a-loc-str a))
        (assoc a ::ret-spec (c/unknown (:form a) (a-loc a)))))))

(s/fdef maybe-strip-meta :args ::analysis :ret ::analysis)
(defn maybe-strip-meta
  "If a is a :op :with-meta, strip it and return the :expr, or a"
  [a]
  (if (-> a :op (= :with-meta))
    (-> a :expr)
    a))

(s/fdef predicate? :args (s/cat :a ::ana.jvm/analysis) :ret boolean?)
(defn var-predicate?
  "True if :def analysis is a predicate."
  [a]
  (when-not (= :def (:op a))
    (println "var-predicate?:" a))
  (assert (= :def (:op a)))
  (let [var-name (:name a)
        def-val (-> a :init (maybe-strip-meta))]
    (if (and (re-find #"\?$" (name var-name))
             (= :fn (:op def-val)))
      (and (-> def-val :methods (count) (= 1))
           (= 1 (-> def-val :methods first :params (count))))
      false)))

(defmethod flow :if [a]
  {:post [(::ret-spec %)]}
  (let [a (-> a
              (update-in [:test] (fn [form] (flow (with-a form a))))
              (update-in [:then] (fn [form] (flow (with-a form a))))
              (update-in [:else] (fn [form] (flow (with-a form a)))))
        then-ret-spec (-> a :then ::ret-spec)
        else-ret-spec (-> a :else ::ret-spec)
        test-ret-spec (-> a :test ::ret-spec)]
    (when-not test-ret-spec
      (println "no ::ret-spec on" (-> a :test :op) (-> a :test :form) (a-loc-str a)))
    (assert test-ret-spec)
    (when (:test a)
      (assert then-ret-spec (format "missing then-ret-spec: %s %s %s" (-> a :then :op) (-> a :then :form)
                                    (a-loc-str a))))
    (when (:else a)
      (assert else-ret-spec (format "missing else-ret-spec: %s %s %s" (-> a :else :op) (-> a :else :form)
                                    (a-loc-str a))))
    (-> a
        (assoc ::ret-spec (if (c/value? test-ret-spec)
                            (if (:v test-ret-spec)
                              then-ret-spec
                              else-ret-spec)
                            (if (= then-ret-spec else-ret-spec)
                              then-ret-spec
                              (c/or- [(-> a :then ::ret-spec)
                                      (-> a :else ::ret-spec)])))))))

(defmethod flow :const [a]
  {:post [(::ret-spec %)]}

  (assoc a ::ret-spec (c/value (:val a))))

(defmethod flow :do [a]
  {:post [(::ret-spec %)]}
  (let [a (-> a
              (update-in [:statements] (fn [statements] (mapv (fn [s]
                                                                (flow (with-a s a))) statements)))
              (update-in [:ret] (fn [ret]
                                  (flow (with-a ret a)))))]
    (assoc a ::ret-spec (-> a :ret ::ret-spec))))

(defmethod flow :try [a]
  {:post [(::ret-spec %)]}
  (update-in a [:body] (fn [body]
                         (flow (with-a body a)))))

(defmethod flow :instance? [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:target] (fn [target]
                                   (flow (with-a target a))))
        s (c/class-spec (:class a))
        arg-spec (-> a :target ::ret-spec)]
    (if (not= (c/unknown? arg-spec))
      (if (c/valid? s arg-spec)
        (assoc a ::ret-spec (c/value true))
        (assoc a ::ret-spec (c/value false)))
      (assoc a ::ret-spec (c/parse-spec #'boolean?)))))

(s/fdef compatible-java-method? :args (s/cat :v ::c/spect :m (s/coll-of (s/or :prim j/primitive? :sym symbol? :cls class?))) :ret boolean?)
(defn compatible-java-method?
  "True if args conforming to spec s can be passed to a method that takes method-types"
  [arg-spec method-types]
  (let [spec (c/cat- (mapv java-type->spec method-types))
        argv (-> arg-spec :ps)]
    (assert argv)
    (c/conform spec argv)))

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
                        (not= ::c/invalid (compatible-java-method? arg-spec (:parameter-types m)))))
             (most-specific))))

(s/fdef get-java-method-spec :args (s/cat :cls class? :method symbol? :arg-spec ::c/spect) :ret ::fn-spec)
(defn get-java-method-spec
  "Return a fake spec for a java interop call"
  [cls method arg-spec a]
  (if-let [m (get-conforming-java-method cls method arg-spec)]
    (let [java-args (->> (mapv java-type->spec (:parameter-types m)))
          ret (c/parse-spec (java-type->spec (:return-type m)))]
      {:args (c/map->RegexCat {:ps (mapv c/parse-spec java-args)
                               :forms java-args
                               :ret []})
       :ret (c/parse-spec ret)})
    (do
      (println "get-java-method-spec: no conforming:" cls method arg-spec "possible:" (mapv :parameter-types (get-java-method cls method)) (a-loc-str a))
      {:args (c/unknown nil)
       :ret (c/unknown nil)})))

(defn flow-java-call
  "Handles both :static-call and :instance-call"
  [a]
  (let [{:keys [class method instance]} a
        a (update-in a [:args] (fn [args]
                                 (mapv (fn [arg]
                                         (flow (with-meta arg {:a a}))) args)))
        args-spec (analysis-args->spec (util/zip a :args))
        spec (get-java-method-spec class method args-spec a)]
    (when-not (:ret spec)
      (println "flow-java-call: no spec:" class method args-spec))
    (assert (:ret spec))
    (-> a
        (assoc ::ret-spec (:ret spec)
               ::args-spec (:args spec)))))

(defmethod flow :static-call [a]
  {:post [(::ret-spec %)]}
  (flow-java-call a))

(defmethod flow :instance-call [a]
  {:post [(::ret-spec %)]}
  (flow-java-call a))

(declare assoc-form-spec)

(s/fdef get-invoke-fn-spec :args (s/cat :a ::analysis) :ret (s/nilable ::c/spect))

(defn get-invoke-fn-spec
  "Given an :fn a, return the spec"
  [a]
  (when (-> a :op (= :var))
    (assert (var? (:var a))))

  (condp = (:op a)
    :var (get-var-fn-spec (:var a))))

(defn assoc-invoke-var [a]
  (let [v (-> a :fn :var)
        _ (assert v)
        s (get-var-fn-spec v)]
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

(s/fdef assoc-spec-bindings :args (s/cat :a ::analysis) :ret ::analysis)
(defn assoc-spec-bindings
  "Given the :bindings from a let, assoc ::flow/spec to the binding, based on the right-hand value"
  [a]
  (reduce (fn [a b]
            (update-in a [:bindings] conj (flow (with-meta b {:a a})))) (assoc a :bindings []) (:bindings a)))

(defmethod flow :local [a]
  {:post [(::ret-spec %)]}
  (let [b (find-binding a (:name a))]
    (assert b)
    (assert b (format "flow :local: failed to find binding: %s %s" (:name a) (a-loc-str a)))
    (when-not (::ret-spec b)
      (println "error: no ret-spec on:" (:name b) (:op b)))
    (assert (::ret-spec b))
    (assoc a ::ret-spec (::ret-spec b))))

(defmethod flow :binding [a]
  {:post [(::ret-spec %)]}
  (let [a (-> a
              (update-in [:init] (fn [init]
                                   (flow (with-a init a)))))]
    (when (and (-> a :init) (-> a :init ::ret-spec not))
      (println "error: no ret-spec on:" (:name a) (:op a) (a-loc-str a)))
    (when (:init a)
      (assert (-> a :init ::ret-spec)))
    (assoc a ::ret-spec (-> a :init ::ret-spec))))

(defn flow-loop-let [a]
  {:post [(::ret-spec %)]}
  (let [a (assoc-spec-bindings a)
        a (update-in a [:body] (fn [body] (flow (with-a body a))))
        ret-spec (::ret-spec (:body a))]
    (assert ret-spec)
    (-> a
        (assoc ::ret-spec ret-spec))))

(defmethod flow :let [a]
  {:post [(::ret-spec %)]}
  (flow-loop-let a))

(defmethod flow :loop [a]
  {:post [(::ret-spec %)]}
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
        (if-let [spec* (c/derivative spec (c/parse-spec (c/will-accept spec)))]
          (recur spec* (rest args))
          false)))
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

(defmethod flow :fn-method [a]
  ;;{:post [(::ret-spec %)]}
  (let [v (-> a meta :a ::var)
        s (when v
            (get-var-fn-spec v))
        a (if s
            (update-in a [:params] destructure-fn-params (:args s) a)
            (update-in a [:params] (fn [params]
                                     (mapv (fn [p]
                                             (assoc p ::ret-spec (c/unknown (:name p) (a-loc a)))) params))))]
    (-> a
        (update-in [:body] (fn [body]
                             (flow (with-meta body {:a a})))))))

(defmethod flow :vector [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:items] (fn [items]
                                  (mapv (fn [i]
                                          (flow (with-a i a))) items)))]
    (assoc a ::ret-spec (mapv ::ret-spec (:items a)))))

(defmethod flow :map [a]
  {:post [(::ret-spec %)]}
  (-> a
      (update-in [:keys] (fn [keys]
                           (mapv (fn [k]
                                   (flow (with-a k a))) keys)))
      (update-in [:vals] (fn [vals]
                           (mapv (fn [v]
                                   (flow (with-a v a))) vals)))
      (assoc ::ret-spec (if (:literal? a)
                          (c/value (:form a))
                          (c/parse-spec #'map?)))))

(defrecord Recur [args])
(defn recur-args [args]
  (map->Recur {:args args}))

(defmethod flow :recur [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:exprs] (fn [exprs]
                                  (mapv (fn [e]
                                          (flow (with-a e a))) exprs)))]
    (assoc a ::ret-spec (recur-args (analysis-args->spec (:exprs a))))))

(defrecord Throw [args])

(defn throw-args [args]
  (map->Throw {:args args}))

(defmethod flow :throw [a]
  {:post [(::ret-spec %)]}
  (let [a (update-in a [:exception] (fn [e]
                                      (flow (with-a e a))))]
    (assoc a ::ret-spec (recur-args (:exception a)))))

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
       (c/keys? target-ret-spec) (or (get-in target-ret-spec [:req-un k])
                                     (get-in target-ret-spec [:opt-un k])))
     (c/unknown (:form a) (a-loc a)))))

(defmethod flow :keyword-invoke [a]
  {:post [(::ret-spec %)]}
  (assoc a ::ret-spec (keyword-invoke-ret-spec a)))

(defmethod flow :new [a]
  {:post [(::ret-spec %)]}
  (assoc a ::ret-spec (c/class-spec (-> a :class :val))))

(defn analyze+flow [form]
  (flow (ana.jvm/analyze form)))

(defn analyze+flow-ns [ns]
  (mapv flow (ana.jvm/analyze-ns ns)))
