(ns spectrum.check
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pprint :refer (pprint)]
            [clojure.reflect :as reflect]
            [clojure.string :as str]
            [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.analyzer-spec]
            [spectrum.conform :as c]
            [spectrum.core-specs]
            [spectrum.analyzer :as analyzer]
            [spectrum.classpath :as classpath]
            [spectrum.types :as t]
            [spectrum.data :as data :refer (*a*)]
            [spectrum.flow :as flow]
            [spectrum.util :as util :refer (zip with-a unwrap-a print-once)]))

(defrecord CheckError [message file line column end-column])

(s/def ::message string?)

(s/fdef check-error? :args (s/cat :x any?) :ret boolean?)
(defn check-error? [x]
  (instance? CheckError x))

(s/fdef map->CheckError :args (s/cat :m (s/keys :req-un [::message])) :ret check-error?)

(s/fdef new-error :args (s/cat :data (s/keys :req-un [::message]) :a ::flow/analysis) :ret check-error?)
(defn new-error [{:keys [message form data] :as args} a]
  (map->CheckError (merge args (select-keys (:env a) [:file :line :column]))))

(s/def ::maybe-check-error (s/nilable check-error?))

(s/def ::check-errors (s/* check-error?))

(s/fdef check* :args (s/cat :a ::flow/analysis) :ret ::check-errors)

(defmulti check* "Entrypoint into low level checking. Takes a tools.analyzer expression. Returns nil or an error" :op)

(declare check)

(def builtin-nses '[clojure.core clojure.set clojure.string clojure.spec.alpha clojure.spec.gen.alpha])

(defn maybe-load-clojure-builtins []
  (when-not (data/analyzed-ns? (find-ns 'clojure.core))
    (println "loading clojure")
    (doseq [n builtin-nses]
      (flow/analyze-cache-ns n))
    (flow/analyze-cache-resource (io/resource "clojure/core_deftype.clj"))))

(s/fdef check :args (s/cat :ns symbol?) :ret ::check-errors)

(defn check-ns [ns]
  (maybe-load-clojure-builtins)
  (println "checking " ns)
  (some->>
   (analyzer/analyze-ns-1 ns (ana.jvm/empty-env))
   (map flow/infer)
   (mapcat check*)
   (filter identity)))

(defn check-common [a]
  (let [ret (::flow/ret-spec a)]
    (assert ret)
    (when (t/invalid? ret)
      [(new-error (merge {:message "unknown"} (select-keys ret [:message :form])) a)])))

(s/fdef check-walk :args (s/cat :a ::flow/analysis) :ret ::check-errors)
(defn check-walk [a]
  (try
    (concat (check-common a)
            (mapcat (fn [c-name]
                      (let [c (get a c-name)]
                        (if (sequential? c)
                          (mapcat (fn [x]
                                    (check* (with-a x a))) c)
                          (check* (with-a c a))))) (:children a)))
    (catch Exception e
      (println "Exception at" (flow/a-loc-str a) (:form a) (.getMessage e))
      (throw e))))

(defmethod check* :default [a]
  (check-walk a))

;; (defn check-fn-method-return [method-a]
;;   (let [f (unwrap-a method-a)
;;         v (::flow/var f)]
;;     (when v
;;       (let [ret-spec (:ret (c/get-var-spec v))
;;             body (-> method-a :body)
;;             last-expr (if (map? body)
;;                         body
;;                         (do
;;                           (assert (sequential? body))
;;                           (last body)))
;;             expr-spec (::flow/ret-spec method-a)]
;;         (when (and ret-spec (c/known? ret-spec))
;;           (if expr-spec
;;             (when-not (c/valid-return? ret-spec expr-spec)
;;               [(new-error {:message (format "%s return value does not conform. Expected %s, Got %s" (or v "fn") (print-str ret-spec) (print-str expr-spec))} method-a)])
;;             [(new-error {:message (format "check-fn-method-return no ret-spec for expression:" (:form last-expr))} last-expr)]))))))

;; (defn check-deftype-method-return [a]
;;   (let [deftype (unwrap-a a)
;;         cls (:class-name deftype)
;;         method-spec (flow/defmethod-get-spec cls (:interface a) (:name a) (rest (:params a)))
;;         method-ret (:ret method-spec)]
;;     (when (and method-ret (c/known? (::flow/ret-spec a)) (not (c/valid-return-java? method-ret (::flow/ret-spec a))))
;;       [(new-error {:message (format "deftype %s implementation of %s/%s return value does not conform. Expected %s, Got %s" cls (:interface a) (:name a) (print-str method-ret) (print-str (::flow/ret-spec a)))}
;;                   a)])))

;; (defn params-str [a]
;;   (->> a :params (mapv :form)))

;; (defmethod check* :fn-method [a]
;;   (concat
;;    (check-walk a)
;;    (check-fn-method-return a)))

;; (defmethod check* :method [a]
;;   (concat
;;    (check-walk a)
;;    (check-deftype-method-return a)))

;; (defn a->java-static-method-name [a]
;;   (str (:class a) "/" (:method a)))

;; (defn java-methods-str [cls method]
;;   (->> (flow/get-java-method cls method)
;;        (mapv :parameter-types)
;;        (str/join ", ")))

;; (s/fdef java-call :args (s/cat :a ::flow/analysis) :ret ::check-errors)
;; (defn maybe-check-defmethod [a]
;;   (if (flow/defmethod? a)
;;     (let [[dispatch-val f] (:args a)]
;;       ;; TODO flow-default, check-default, :children. defmethod checking is broken because we don't recurse automatically.
;;       ;;
;;       )
;;     nil))

;; (s/fdef java-call :args (s/cat :a ::flow/analysis) :ret ::check-errors)
;; (defn java-call [a]
;;   (let [a-args (zip a :args)
;;         args-spec (flow/analysis-args->spec a-args)
;;         call-spec (::flow/args-spec a)
;;         ret-spec (::flow/ret-spec a)]
;;     (concat
;;      (cond
;;        (c/unknown? ret-spec) nil
;;        (c/conformy? ret-spec) nil
;;        (c/invalid? ret-spec) [(new-error ret-spec a)])
;;      (maybe-check-defmethod a))))

;; (defmethod check* :instance-call [a]
;;   (concat
;;    (check-walk a)
;;    (java-call a)))

;; (defmethod check* :static-call [a]
;;   (concat
;;    (check-walk a)
;;    (java-call a)))

;; ;; check recur values conform to bindings

;; (defn type-of
;;   "Given a quoted form, returns spectrum's expected type for evaluating the form"
;;   ([form]
;;    (->> (analyze-form form)
;;         ::flow/ret-spec))
;;   ([form specs]
;;    (->> (analyze-form form specs)
;;         ::flow/ret-spec)))

;; (defn check-form
;;   "Given a quoted form, returns any typechecking errors, or nil"
;;   ([form]
;;    (->> (analyze-form form)
;;         (check*)))
;;   ([form specs]
;;    (->> (analyze-form form specs)
;;         (check*))))
