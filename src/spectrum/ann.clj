(ns spectrum.ann
  (:require [clojure.java.io :as io]
            [clojure.spec.alpha :as s]
            [spectrum.conform :as c]
            [spectrum.data :as data :refer [ann]]
            [spectrum.java :as j]
            [spectrum.types :as t]
            [spectrum.util :refer (print-once validate!)])
  (:import (clojure.lang BigInt
                         Ratio
                         IPersistentCollection
                         ISeq
                         LazySeq
                         Seqable)
           (java.util Map)))


(s/fdef ann-instance? :args (s/cat :v var? :c class?))
(defn ann-instance?
  "Annotates var-predicate v as just a simple instanceof? check

   (ann-instance #'string? java.lang.String)
 "
  [v cls]
  (ann v (t/fn-t {[(t/class-t cls)] (t/value-t true)
                  [(t/not-t (t/class-t cls))] (t/value-t false)}))
  (t/set-equiv-types! (t/class-t cls) v))

(s/fdef ann-instance-or? :args (s/cat :v var? :c (s/coll-of class?)))
(defn ann-instance-or?
  "Ann var-predicate v as (some #(instance? c x) clses)"
  [v clses]
  (ann v (t/fn-t {[(t/or-t (mapv t/class-t clses))] (t/value-t true)
                  [#'any?] (t/value-t false)}))
  (t/set-equiv-types! (t/or-t (mapv t/class-t clses)) v))

(s/fdef ann-method :args (s/cat :c class? :n symbol? :t ::type))
(defn ann-method
  "Annotate a java method. This replaces all arities, so t should
  accept all arities the method accepts (and reject signatures the method rejects!)"
  [cls method t]
  (assert (seq (j/get-java-method cls method)))
  (data/ann [cls method] t))

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

(t/set-equiv-types! (t/value-t nil) #'nil?)
(t/set-equiv-types! (t/value-t true) #'true?)
(t/set-equiv-types! (t/value-t false) #'false?)
(t/set-equiv-types! (t/value-t 0) #'zero?)

(t/derive-type #'number? #'integer?)
(t/derive-type #'number? #'double?)
(t/derive-type #'integer? #'int?)
(t/derive-type #'integer? #'even?)
(t/derive-type #'integer? #'odd?)
(t/derive-type #'number? #'neg?)
(t/derive-type #'number? #'pos?)

(t/derive-type #'ifn? #'fn?)

(t/derive-type 'coll-of 'vector-of)

(t/derive-type #'keyword? #'simple-keyword?)
(t/derive-type #'keyword? #'qualified-keyword?)

(t/derive-type #'symbol? #'qualified-symbol?)
(t/derive-type #'symbol? #'simple-symbol?)

(ann-instance-or? #'float? [Float Double])
(ann-instance-or? #'int? [Long Integer Short Byte])
(ann-instance-or? #'integer? [Long Integer Short Byte clojure.lang.BigInt BigInteger])
(ann-instance-or? #'seqable? [clojure.lang.ISeq clojure.lang.Seqable Iterable CharSequence java.util.Map]) ;; TODO java array

(ann #'seq (t/fn-t {[(t/seq-of '?x)] (t/seq-of '?x)
                    [(t/class-t Iterable)] (t/seq-of '?x)
                    [(t/class-t CharSequence)] (t/seq-of (t/class-t Character))
                    [(t/class-t Map)] (t/seq-of (t/cat-t ['?k '?v]))
                    [(t/map-of '?x '?y)] (t/seq-of (t/cat-t ['?x '?y]))
                    ;; todo array-of
                    [(t/class-t Seqable)] (t/seq-of '?x)
                    }))

(ann #'cons (t/fn-t {['?x #'nil?] (t/and-t [(t/cat-t ['?x]) (t/class-t ISeq)])
                     ['?x (t/seq-of '?y)] (t/and-t [(t/cat-t ['?x (t/seq-of '?y)]) (t/class-t ISeq)])
                     ['?x #'seqable?] (t/and-t [(t/cat-t ['?x (t/seq-of '?y)]) (t/class-t ISeq)])}))

(ann #'first (t/fn-t {[(t/spec-t (t/seq-of '?a))] (t/or-t ['?a #'nil?])
                      [#'seqable?] (t/or-t ['?x #'nil?])}))

(ann #'next (t/fn-t {[(t/spec-t (t/seq-of '?a))] (t/or-t [(t/seq-of '?a) #'nil?])
                     [#'seqable?] (t/or-t ['?x #'nil?])}))

(ann #'rest (t/fn-t {[(t/spec-t (t/seq-of '?a))] (t/or-t [(t/seq-of '?a) #'nil?])
                     [#'seqable?] (t/or-t ['?x #'nil?])}))

(ann #'apply (t/fn-t {['?f (t/spec-t (t/cat-t ['?a]))] (t/invoke-t '?f (t/cat-t ['?a]))
                      ['?f (t/spec-t (t/cat-t ['?a '?b]))] (t/invoke-t '?f (t/cat-t ['?a '?b]))
                      ['?f (t/spec-t (t/cat-t ['?a '?b '?c]))] (t/invoke-t '?f (t/cat-t ['?a '?b '?c]))
                      ['?f '?a (t/spec-t (t/seq-of '?b))] (t/invoke-t '?f (t/cat-t ['?a (t/seq-of '?b)]))}))

(ann #'keyword (t/fn-t {[(t/or-t [#'keyword? #'symbol? #'string?])] #'simple-keyword?
                        [(t/not-t (t/or-t [#'keyword? #'symbol? #'string?]))] #'nil?
                        [#'string? #'string?] #'qualified-keyword?}))

(ann-method clojure.lang.Util 'identical (t/fn-t {['[value ?x] '[value ?x]] ['value true]
                                                  ['[value ?x] '[value ?y]] ['value false]
                                                  [#'any? #'any?] ['class Boolean/TYPE]}))

(ann-method clojure.lang.Util 'equiv (t/fn-t {['[value ?x] '[value ?x]] ['value true]
                                              ['[value ?x] '[value ?y]] ['value false]
                                              ['?a '?b] ['class Boolean/TYPE]} ))

;; we'd prefer to infer map, but it needs dependent types to handle the chunked-seq case
(ann #'map (t/fn-t {[(t/fn-t {['?x] '?y}) (t/spec-t (t/seq-of '?x))] (t/and-t [(t/seq-of '?y) (t/class-t LazySeq)])
                    [(t/fn-t {['?x1 '?x2] '?y}) (t/spec-t (t/seq-of '?x1)) (t/spec-t (t/seq-of '?x2))] (t/and-t [(t/seq-of '?y) (t/class-t LazySeq)])}))
