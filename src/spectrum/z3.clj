(ns spectrum.z3
  (:refer-clojure :exclude [eval test pop assert])
  (:require [clojure.core :as c]
            [clojure.edn :as edn]
            [clojure.pprint :refer [pprint]]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [net.n01se.clojure-jna :as jna]
            [spectrum.util :as u]
            [wall.hack])
  (:import [com.microsoft.z3 Global Context Native]))

(defn nctx [ctx]
  (wall.hack/method Context :nCtx [] ctx))

(defn new-context
  ([]
   (Context.))
  ([{:strs [unsat_core model] :as options}]
   (Context. options)))

(defn set-global-param! [k v]
  (Global/setParameter k v))

(def current-context (atom (new-context)))

(defn set-context! [ctx]
  (reset! current-context ctx))

(defn context? [x]
  (instance? Context x))

(defn parse-response-dispatch [form response]
  (when (coll? form)
    (first form)))

(defmulti parse-response #'parse-response-dispatch)

(def ^:dynamic *throw-errors* true)

(defn eval
  ([form]
   {:pre [(context? @current-context)]}
   (eval @current-context form))
  ([ctx form]
   {:pre [(context? ctx)]}
   (let [form-s (pr-str form)
         _ (c/assert (= form (edn/read-string form-s)))
         resp (wall.hack/method Native :INTERNALevalSmtlib2String [Long/TYPE String] nil (nctx ctx) (binding [*print-level* nil
                                                                                                              *print-length* nil]
                                                                                                      form-s))]
     (println "eval" form-s)
     resp
     (if (and *throw-errors* (coll? resp) (= 'error (first resp)))
       (throw (ex-info (print-str "error evaling" form) {:form form :response resp}))
       (parse-response form resp)))))

(defn maybe-throw [cmd resp]
  (if-let [msg (cond
                 (and (coll? resp) (= 'error (first resp))) (second resp)
                 (= 'unsupported resp) (str resp)
                 :else nil)]
    (throw (ex-info msg {:command cmd
                          :error resp}))
    resp))

(defmethod parse-response 'set-option [cmd response]
  response)

(defmethod parse-response :default [cmd response]
  (let [resp (edn/read-string response)]
    (c/assert resp (print-str "no response from" cmd))
    (maybe-throw cmd resp)
    resp))

(defmethod parse-response 'check-sat [_ response]
  (condp = (edn/read-string response)
    'sat :sat
    'unsat :unsat
    'unknown :unknown
    response;; (c/assert false (pr-str "unrecognized response:" response))
    ))

(defn print-output [resp]
  (doseq [l (str/split resp #"\n")]
    (println l)))

(defmethod parse-response 'help [_ resp]
  (print-output resp))

(defmethod parse-response 'help-tactic [_ resp]
  (print-output resp))

(defmethod parse-response 'get-proof [_ resp]
  (doseq [l (str/split resp #"\n")]
    (println l)))

(defn serialize-dispatch [x]
  (cond
    (var? x) #'var?
    (vector? x) #'vector?
    :else x))

(defmulti ->z3 #'serialize-dispatch)

(defmethod ->z3 :default [x]
  x)

(defmethod ->z3 #'var? [x]
  (u/var-name x))

(defmethod ->z3 #'vector? [x]
  (list* x))

(defn- unquote?
  "Tests whether the form is (unquote ...)."
  [form]
  (and (coll? form) (= 'clojure.core/unquote (first form))))

(defn unquote-splicing? [form]
  (and (coll? form) (= 'clojure.core/unquote-splicing (first form))))

(declare inner-walk outer-walk)

(defn q-walk [f]
  (walk/walk inner-walk outer-walk f))

(defn- inner-walk [form]
  ;; {:post [(do (println "inner-walk" form "=>" %) true)]}
  (cond
    (unquote? form) [(second form)]
    (unquote-splicing? form) (second form)
    :else [(q-walk form)]))

(defn- outer-walk [form]
  ;; {:pre [(do (println "outer-walk") true)]
  ;;  :post [(do (println "outer-walk" form "=>" %) true)]}
  (cond
    (symbol? form) (list 'quote form)
    (seq? form) (list* 'concat form)
    :else form))

(defmacro q
  "quasiquote. Doesn't resolve symbols, so e.g. (q (inc ~x)) returns '(inc 1) rather than '(clojure.core/inc 1)"
  [form]
  ;; {:post [(do (println "q:" form "=>" %) true)]}
  (let [post-form (q-walk form)]
    post-form))

(defmacro def-smt-fn
  [name]
  {:pre [(symbol? name)]}
  `(defmacro ~name [& args#]
     (let [name# (quote ~name)
           form# (list name# args#)]
       `(do
          (println "def-smt-fn eval" @current-context (quote ~form#))
          (eval @current-context (q (~name# ~@args#)))))))

(defmacro def-smt-fns [fns]
  (println "def-smt-fns" fns)
  (let [forms (->> fns
                   (map (fn [f]
                          `(def-smt-fn ~f))))]
    `(do
     ~@forms)))

(def-smt-fns [assert
              check-sat
              check-sat-assuming
              declare-const
              declare-datatype
              declare-datatypes
              declare-fun
              declare-rel
              declare-var
              declare-sort
              define-fun
              define-fun-rec
              define-sort
              echo
              get-assertions
              get-assignment
              get-consequences
              get-info
              get-model
              get-option
              get-proof
              get-proof-graph
              get-unsat-assumptions
              get-unsat-core
              get-user-tactics
              get-value
              help
              help-tactic
              labels
              pop
              push
              query
              reset
              reset-assertions
              rule
              set-info
              set-logic
              set-option
              simplify])
