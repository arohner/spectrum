(ns spectrum.z3-types
  (:refer-clojure :exclude [test eval pop assert])
  (:require [clojure.core :as c]
            [clojure.spec.alpha :as s]
            [spectrum.z3 :refer :all]
            [spectrum.types :as t]
            [spectrum.util :as u]))

(set-global-param! "unsat_core" "true")
(set-global-param! "model" "true")
(set-global-param! "proof" "true")
(set-global-param! "model_validate" "true")
;; (set-global-param! "dump_models" "true")
(set-global-param! "timeout" "5000")

(def ctx (new-context))

(set-context! ctx)

(set-option :print-success true)
;; (set-option :produce-models true)

(defn predicate-classes
  "all java classes mentioned in equiv-types, ann/instance, etc"
  []
  (let [classes (atom #{})]
    (->> @t/equiv-types
       (spectrum.util/mapwalk (fn [x]
                                (when (class? x)
                                  (swap! classes conj x)))))
    @classes))

(defn all-classes []
  (->>
   (concat
    (predicate-classes)
    (mapcat ancestors (predicate-classes)))
   (distinct)))

(defn all-predicates []
  (t/core-predicates))

(let [preds (->> (t/core-predicates) (map (fn [p] (list (u/var-name p)))))
      classes (predicate-classes)]
  (println "preds:" preds)
  (declare-datatype Type
                    (
                     ~@preds
                     ;; ~@classes
                     ;; (vector-t (vector-value Type))
                     ;; (list-t (list-value Type))
                     )))

(declare-fun parent? (Type Type) Bool)
(declare-fun equiv? (Type Type) Bool)

(defn load-equiv-types []
  (assert (forall ((x Type) (y Type))
                  (= (equiv? x y)
                     (or ~@(for [[k vs] @t/equiv-types
                                 v vs]
                             (q (or (and (= x ~(->z3 k)) (= y ~(->z3 v)))
                                    (and (= y ~(->z3 k)) (= x ~(->z3 v)))))))))))

;; (load-equiv-types)

(defn load-derived-types []
  (doseq [t (disj (all-predicates) #'any?)
          :let [parents (-> t t/parents set ((fn [ps]
                                               (if (seq (disj ps #'any?))
                                                 ps
                                                 #{#'any?}))))
                _ (c/assert (= 1 (count parents)) (print-str t "has parents" parents))
                parent (first parents)]]
    (assert (forall ((x Type))
                    (= (parent? x ~(->z3 t))
                       (= x ~(->z3 parent)))))))

(assert (parent? clojure.core/any? clojure.core/any?))

;; (load-derived-types)

(defn load-class-hierarchy []
  ;; (assert (= clojure.core/any? (parent (class-t java.lang.Object))))
  (assert (parent? java.lang.Object java.lang.Object))
  (doseq [c (all-classes)
          :when (seq (bases c))] ;; interfaces don't need to have parents
    (let [parent-forms (map (fn [pc] (q (= x ~pc))) (bases c))
          parent-forms (if (= 1 (count (bases c)))
                           (first parent-forms)
                           (q (or ~@parent-forms)))]
      (assert (forall ((x Type))
                    (= (parent? x ~c)
                       (= x ~parent-forms)))))))

;; (load-class-hierarchy)

(define-fun subtype? ((x Type) (y Type)) Bool
  (or (= x y)
      (parent? x y)
      ;; (exists ((a Type)) (and (parent? x a) (parent? a y)))
      ;; (exists ((a Type) (b Type)) (and (parent? x a) (parent? a b) (parent? b y)))
      ;; (exists ((a Type) (b Type) (c Type)) (and (parent? x a) (parent? a b) (parent? b c) (parent? c y)))
      ))

(define-fun unify ((x Type) (y Type)) Bool
  (or (= x y) (subtype? x y)))

(defmacro with-pop [& body]
  `(try
     (push)
     ~@body
     (finally
       (pop))))

(defn unify [x y]
  (with-pop
    (declare-const x Type)
    (declare-const y Type)
    (assert (= x ~(->z3 x)))
    (assert (= y ~(->z3 y)))
    (assert (subtype? x y))
    (let [resp (check-sat)]
      (condp = resp
          :sat [(get-model) resp]
          :unsat [(get-proof) resp]
          resp))))

(defn go []
  (check-sat)
  (println "result:" (get-assignment)))

(u/instrument-ns)
