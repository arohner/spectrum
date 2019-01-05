(ns spectrum.ann
  (:require [clojure.java.io :as io]
            [clojure.spec.alpha :as s]
            [spectrum.java :as j]
            [spectrum.types :as t]
            [spectrum.util :refer (print-once validate!)])
  (:import (clojure.lang BigInt
                         Ratio
                         Seqable)
           (java.util Map)))

(def annotations (atom {}))

(s/fdef ann :args (s/cat :v var? :m (s/tuple [class? symbol?]) :t ::t/type))
(defn ann
  "Define a more specific type for the var. `ann` types are preferred
  over explicit specs or inferred types, and if an `ann` exists for a
  var, only it will be consulted"
  [v t]
  (swap! annotations assoc v t)
  nil)

(s/fdef get-ann :args (s/cat :x (s/or :v var? :m (s/tuple [class? symbol?]))) :ret (s/nilable ::t/type))
(defn get-ann [x]
  (get @annotations x))

(s/fdef ann-instance? :args (s/cat :v var? :c class?))
(defn ann-instance?
  "Annotates var-predicate v as just a simple instanceof? check

   (ann-instance #'string? java.lang.String)
 "
  [v cls]
  (ann v (t/fn-t {[(t/class-t cls)] (t/value-t true)
                  [#'any?] (t/value-t false)})))

(defn ann-instance-or?
  "Ann var-predicate v as (some #(instance? c x) clses)"
  [v clses]
  (ann v (t/fn-t {(mapv t/class-t clses) (t/value-t true)
                  [#'any?] (t/value-t false)})))
;;;

(def pred->class
  {#'associative? clojure.lang.Associative
   #'boolean? Boolean
   #'char? Character
   #'chunked-seq? clojure.lang.IChunkedSeq
   #'class? Class
   #'coll? clojure.lang.IPersistentCollection
   #'counted? clojure.lang.Counted
   #'decimal? BigDecimal
   #'delay? clojure.lang.Delay
   #'double? Double
   #'fn? clojure.lang.Fn
   #'future? java.util.concurrent.Future
   #'ifn? clojure.lang.IFn
   #'indexed? clojure.lang.Indexed
   #'inst? java.util.Date
   #'keyword? clojure.lang.Keyword
   #'list? clojure.lang.IPersistentList
   #'map-entry? java.util.Map$Entry
   #'map? clojure.lang.IPersistentMap
   #'number? Number
   #'qualified-symbol? clojure.lang.Symbol
   #'qualified-keyword? clojure.lang.Keyword
   #'ratio? clojure.lang.Ratio
   #'reader-conditional? clojure.lang.ReaderConditional
   #'reversible? clojure.lang.Reversible
   #'seq? clojure.lang.ISeq
   #'sequential? clojure.lang.Sequential
   #'set? clojure.lang.IPersistentSet
   #'sorted? clojure.lang.Sorted
   #'string? String
   #'simple-symbol? clojure.lang.Symbol
   #'simple-keyword? clojure.lang.Keyword
   #'symbol? clojure.lang.Symbol
   #'tagged-literal? clojure.lang.TaggedLiteral
   #'uri? java.net.URI
   #'uuid? java.util.UUID
   #'var? clojure.lang.Var
   #'vector? clojure.lang.IPersistentVector
   #'volatile? clojure.lang.Volatile
   })

(doseq [[v cls] pred->class]
  (ann-instance? v cls))

(ann-instance-or? #'float? [Float Double])
(ann-instance-or? #'int? [Long Integer Short Byte])
(ann-instance-or? #'integer? [Long Integer Short Byte clojure.lang.BigInt BigInteger])
(ann-instance-or? #'seqable? [clojure.lang.ISeq clojure.lang.Seqable Iterable CharSequence java.util.Map]) ;; TODO java array

(s/fdef ann-method :args (s/cat :c class? :n symbol? :t ::type))
(defn ann-method
  "Annotate a java method. This replaces all arities, so t should cover all signatures of the method"
  [cls method t]
  (assert (seq (j/get-java-method cls method)))
  (ann [cls method] t))

(ann #'seq (t/fn-t {[(t/class-t Iterable)] (t/seq-of '?x)
                    [(t/class-t CharSequence)] (t/seq-of (t/class-t Character))
                    [(t/class-t Map)] (t/seq-of (t/cat-t ['?k '?v]))
                    [(t/map-of '?x '?y)] (t/seq-of (t/cat-t ['?x '?y]))
                    ;; todo array-of
                    [(t/class-t Seqable)] (t/seq-of '?x)}))

(ann #'first (t/fn-t {[(t/seq-of '?a)] (t/or-t ['?a #'nil?])
                      [#'seqable?] (t/invoke-t #'first (t/cat-t [(t/invoke-t #'seq (t/cat-t ['?x]))]))
                      [#'any?] #'nil?}))

(ann #'next (t/fn-t {[(t/seq-of '?a)] (t/or-t [(t/seq-of '?a) #'nil?])
                     [#'any?] #'nil?}))
