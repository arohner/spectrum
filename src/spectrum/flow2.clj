(ns spectrum.flow2
  (:require [clojure.core.memoize :as memo]
            [clojure.core.match :refer [match]]
            [clojure.core.unify :as u]
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
            [spectrum.analyzer :as analyzer]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.flow :as f]
            [spectrum.java :as j]
            [spectrum.util :as util :refer [print-once protocol? namespace? queue validate! instrument-ns memoize-with]]
            [spectrum.unify :as u2])
  (:import [clojure.lang Var Namespace]))

(defn new-context []
  {:typenames (atom {})
   :counter (atom 0)})

(defn new-type [context]
  (let [next (-> context :counter (swap! inc))]
    (c/new-logic next)))

(defn store-type! [context t a path]
  (-> context :typenames (swap! assoc [a path] t)))

(defn analyze-form
  "Analyze a form.

   (analyze-form '(string? 3))

   Optionally takes a map of keywordized variables to specs:

   (analyze-form '(string? x) {:x (c/pred-spec #'string?)})
  "
  ([form]
   (analyze-form form {}))
  ([form specs]
   (let [locals (into {} (map (fn [[binding spec]]
                                (let [binding (symbol (name binding))]
                                  [binding {:op :binding
                                            :name binding
                                            :form binding
                                            :env {}
                                            :local :let
                                            ::ret-spec spec}])) specs))]
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
  "Given an analysis a, recursively call f on a, and all of a's `:children`. Return a seq of all `f` return values"
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
  (new-type context))

(defmethod create-typename :binding [context a path]
  (let [t (new-type context)
        a* (get-in a path)]
    (assert (:atom a*))
    (swap! (:atom a*) assoc ::t t)
    t))

(defn assign-typenames
  "Walk the analysis, assign type names to every expression"
  [context a]
  (walk-a-rec (fn [a path]
                (let [t (create-typename context a path)]
                  (store-type! context t a path))) a))

(defn get-equations-dispatch [context a path]
  (:op (get-in a path)))

(s/def ::equation (s/tuple c/spect? c/spect?))
(s/def ::equations (s/coll-of ::equation))

(defmulti get-equations* #'get-equations-dispatch)

(defmethod get-equations* :default [context a path]
  (let [a* (get-in a path)]
    (assert a*)
    (println "no equations for" (:form a*) (:op a*)))
  [])

(defn get-type-dispatch [context a path]
  (-> a (get-in path) :op))

(defmulti get-type* #'get-type-dispatch)

(defmethod get-type* :default [context a path]
  {:post [(do (when-not %
                (println "get-type: no type for" path (:form (get-in a path)))) true)
          %]}
  (-> context :typenames deref (get [a path])))

(defmethod get-type* :local [context a path]
  {:post [%]}
  (let [a* (get-in a path)]
    (assert a*)
    (-> a* :atom deref ::t)))

(defmethod get-equations* :const [context a path]
  (let [a* (get-in a path)
        t (get-type* context a path)]
    [[t (c/value (:form a*))]]))

(defmethod get-equations* :binding [context a path]
  (let [a* (get-in a path)
        t (get-type* context a path)]
    (if (:init a*)
      [[t (get-type* context a (conj path :init))]]
      [])))

(defmethod get-equations* :local [context a path]
  [])

(defn map-sequential-children
  "Call `(f context a $path)` on each sequential child of (-> a (get-in path) key)"
  [f context a path key]
  (map (fn [i]
         (f context a (conj path key i))) (-> a (get-in (conj path key)) count range)))

(defmethod get-equations* :fn-method [context a path]
  (let [a* (get-in a path)
        t (get-type* context a path)
        ret-type (get-type* context a (conj path :body))]
    [[t (c/fn-spec {:args (c/cat- (map-sequential-children get-type* context a path :params))
                    :ret ret-type})]]))

(defmethod get-equations* :fn [context a path]
  (let [a* (get-in a path)
        t (get-type* context a path)]
    [[t (c/or- (map-sequential-children get-type* context a path :methods))]]))

(defmethod get-equations* :let [context a path]
  (let [a* (get-in a path)
        t (get-type* context a path)]
    [[t (get-type* context a (conj path :body))]]))

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
  (let [a* (get-in a path)
        {:keys [class method instance]} a*]
    (if (and class method)
      (let [cls-arg (if (:instance a*)
                      (-> a* :instance ::ret-spec)
                      (-> a* :class (c/value)))
            invoke-args (c/cat- (concat [cls-arg] (mapv (fn [i] (get-type* context a (conj path :args i))) (range (count (:args a*))))))
            methods (f/get-java-method class method)
            method-specs (map (fn [m]
                                [m (f/method->spec m)]) methods)
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
                         transformed-spec))]
        (if (c/conformy? transformed-spec)
          (let [spec-args (c/all-possible-values-length-n (:args transformed-spec) (inc (count (:args a*))))
                arg-pairs (map vector (concat [(:instance a*)] ) (c/elements spec-args))]
            (concat
             (if-let [inst (get-in a (conj path :instance))]
               [(get-type* context a (conj path :instance)) (first (c/elements spec-args))]
               [])
             (map (fn [i s]
                    (let [arg-type (get-type* context a (conj path :args i))]
                      [arg-type s]))
                  (range (count (:args a*))) (rest (c/elements spec-args)))
             [[(get-type* context a path) (:ret transformed-spec)]]))
          []))
      (do
        (println "infer java call:" (:form a*) class method instance "unknown")
        []))))

(defmethod get-equations* :static-call [context a path]
  (get-equations-java-call context a path))

(defmethod get-equations* :instance-call [context a path]
  (get-equations-java-call context a path))

(defn get-spec-for-invoke [a path]
  (let [a* (get-in a path)
        v (get-in a (concat path [:fn :var]))]
    (or (when v
          (c/get-var-spec v))
        ;; (when f-a
        ;;   (-> (get-in f-a f-a-path) ::ret-spec))
        ;; (when f-a
        ;;   (invoke-get-fn-spec a path))
        ;; (println "infer invoke couldn't find spec for" (:form a*))
        )))

(defmethod get-equations* :invoke [context a path]
  {:post [(do (println "get-eq invoke:" (:form (get-in a path)) "=>" %) true)
          (s/valid? ::equations %)]}
  (let [a* (get-in a path)
        args (:args a*)
        s (get-spec-for-invoke a path)
        s-args (c/invoke-accept s)
        s-args (c/all-possible-values-length-n s-args (c/min-length s-args))]
    (assert s)
    (->>
     (concat
      (map (fn [i s-a]
             (let [arg-path (conj path :args i)
                   arg-node (get-in a arg-path)
                   _ (assert arg-node)
                   t (get-type* context a arg-path)]
               (println "invoke:" (:form arg-path) "=>" t)
               (assert t)
               [t s-a])) (map vector (range (count (:args a*))) (c/elements s-args)))
      (when (:ret s)
        (let [t (get-type* context a path)]
          (println "invoke: ret =>" t)
          [[t (:ret s)]])))
     (filterv identity))))

(defn get-equations [context a]
  (walk-a-rec (fn [a path]
                (assert (get-in a path))
                (get-equations* context a path)) a))

(defn resolve-type
  "Look up the type of t. If it maps to a type variable, recursively resolve"
  [subst t]
  (let [t* (get subst t)]
    (if (c/fn-spec? t*)
      (-> t*
          (update-in [:args] (fn [args]
                               (assert (c/cat? args))
                               (c/cat- (map (fn [a]
                                              (or (resolve-type subst a) a)) (c/elements args)))))
          (update-in [:ret] (partial resolve-type subst)))
      (if (c/logic? t*)
        (recur subst t*)
        t*))))

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

(defn unify-all-equations [eqs]
  (let [subst {}]
    (reduce (fn [subst eq]
              (let [[l r] eq]
                (u2/unify l r subst))) subst eqs)))

(defn infer-form [form]
  (let [a (analyze-form form)
        context (new-context)]
    (assign-typenames context a)
    (let [eq (apply concat (get-equations context a))
          eq* (consolidate-equations eq)
          subst (unify-all-equations eq*)
          t (get-type* context a [])]
      (println "unify:" subst)
      (resolve-type subst t))))

(instrument-ns)
