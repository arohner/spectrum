(ns spectrum.compiler-test
  (:refer-clojure :exclude [gen-class])
  (:require [clojure.spec.alpha :as s]
            [clojure.test :refer :all]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.clojure-test :refer [defspec]]
            [spectrum.compiler :as c]
            [spectrum.java :as java]
            [spectrum.util :refer [validate!]]))

(def gen-pred (gen/elements
               [#'any?
                #'boolean?
                #'bytes?
                #'char?
                #'coll?
                #'decimal?
                #'delay?
                #'double?
                #'false?
                #'float?
                #'fn?
                #'ident?
                #'ifn?
                #'indexed?
                #'inst?
                #'int?
                #'integer?
                #'pos-int?
                #'neg-int?
                #'keyword?
                #'list?
                #'map?
                #'nat-int?
                #'nil?
                #'number?
                #'pos-int?
                #'qualified-keyword?
                #'qualified-symbol?
                #'ratio?
                #'rational?
                #'seq?
                #'seqable?
                #'set?
                #'simple-ident?
                #'simple-keyword?
                #'simple-symbol?
                #'string?
                #'symbol?
                #'true?
                #'uuid?
                #'var?
                #'vector?]))

(def gen-class (gen/elements [Object
                              String
                              Integer
                              Long
                              clojure.lang.Keyword
                              Boolean
                              clojure.lang.Ratio
                              java.math.BigDecimal
                              Character
                              java.util.Map
                              clojure.lang.ISeq]))

(def gen-type (gen/one-of [;; gen-class
                           gen-pred]))

;; (defspec types-gen 100
;;   (prop/for-all [t gen-type]
;;     (boolean (seq (gen/sample (s/gen (c/spec t)))))))

;; (defspec types-have-ancestors 100
;;   (prop/for-all [t (gen/such-that (fn [t]
;;                                     (and (not= Object t)
;;                                          (not= #'any? t))) gen-type)]
;;     (boolean (seq (c/ancestors t)))))

;; (defspec types-match-specs 100
;;   (prop/for-all [a gen-type
;;                  b gen-type]
;;     (let [as (c/spec a)
;;           bs (c/spec b)
;;           bv (gen/generate (s/gen bs))
;;           s-valid? (s/valid? as bv)
;;           conformed? (boolean (c/valid? a b))]
;;       (= s-valid? conformed?))))

;; (deftest predicate-child?
;;   (is (c/predicate-descendant? #'number? #'pos-int?)))

(declare gen-analysis)

(def gen-const
  (gen/fmap (fn [v]
              {:op :const
               :literal? true
               :val v
               :children []}) (s/gen any?)))

(def gen-name (gen/fmap symbol (gen/such-that seq gen/string-alphanumeric) ))

(defn gen-let-binding [gen-args]
  (gen/fmap (fn [[name form]]
              {:op :binding
               :name name
               :local :let
               :init form
               :atom (atom nil)
               :children [:init]}) (gen/tuple gen-name (gen-analysis (update gen-args :depth dec)))))

(defn gen-let-bindings [gen-args]
  (gen/vector (gen-let-binding gen-args) 0 3))

(defn gen-do [{:keys [depth] :as args}]
  (let [args (update args :depth dec)]
    (gen/fmap (fn [forms]
                {:op :do
                 :statements (vec (butlast forms))
                 :ret (last forms)
                 :children [:statements :ret]}) (gen/vector (gen-analysis args) 1 3))))

(defn gen-let [{:keys [depth locals] :as gen-args}]
  (gen/bind (gen-let-bindings gen-args)
            (fn [bindings]
              (let [gen-body (-> gen-args
                                 (update :depth dec)
                                 (update :locals (fn [locals]
                                                   (merge locals (into {} (map (fn [b] [(:name b) (:atom b)]) bindings)))))
                                 gen-do)]
                (gen/fmap (fn [body]
                            {:op :let
                             :bindings bindings
                             :body body})
                          gen-body)))))

(defn gen-let-local [{:keys [locals] :as args}]
  (gen/fmap (fn [[name a]]
              {:op :local
               :local :let
               :name name
               :atom a
               :assignable? false}) (gen/elements locals)))

(defn gen-fn-arg-local [{:keys [fn-args] :as gen-args}]
  (gen/fmap (fn [{:keys [arg-id variadic? atom] :as arg}]
              (assert (:atom arg))
              {:op :local
               :local :arg
               :arg-id arg-id
               :variadic? variadic?
               :atom atom}) (gen/elements fn-args)))

(def gen-meta (s/gen (s/map-of any? any?)))

(def the-test-ns (create-ns 'spectrum.compiler-test-data))

(defn gen-def [{:keys [depth] :as args}]
  (gen/fmap (fn [[name meta init]]
              {:op :def
               :name name
               :var (intern the-test-ns name)
               :init init
               :meta meta
               }) (gen/tuple gen-name gen-meta (if (pos? depth)
                                                           (gen-analysis (update args :depth dec))
                                                           (gen/return nil)))))

(defn gen-analysis [{:keys [depth locals fn-args] :as gen-args}]
  (let [forms (concat
               [gen-const]
               (when (seq locals)
                 [(gen-let-local gen-args)])
               (when (seq fn-args)
                 [(gen-fn-arg-local gen-args)])
               (when (pos? depth)
                 (let [gen-args (update gen-args :depth dec)]
                   [(gen-let gen-args)
                    (gen-do gen-args)
                    (gen-def gen-args)])))]
    (gen/one-of forms)))

(defspec compiler-works
  (prop/for-all [a (gen-analysis {:depth 2})]
    (let [f (c/compile* a)
          rets (f (c/new-env))]
      (and (fn? f)
           (validate! ::c/envs rets)))))

(deftest things-work
  (let [rets (c/test-invoke #'integer? [(c/fresh "t")])]
    (is (= 7 (count rets)))
    ))

(deftest constructors
  (is (-> (java/get-constructors String 1)
       last
       c/compile-constructor
       (.invoke c/*env*)
       (.invoke String)
       ::c/error
       not))

  (is (-> (java/get-constructors String 1)
       last
       c/compile-constructor
       (.invoke c/*env*)
       (.invoke Integer)
       ::c/error)))
