(ns spectrum.core-specs
  (:require [clojure.core :as core]
            [clojure.spec.alpha :as s]
            [spectrum.ann :as ann]
            [spectrum.util :refer (protocol? predicate-spec def-instance-predicate)])
  (:import (java.lang Iterable)
           (java.util Map)
           (clojure.lang ISeq
                         Seqable)))

;;; specs for clojure.core fns, used as hacks/testing. Delete when official versions become available

(defn namespace? [x] (instance? clojure.lang.Namespace))

(defn array? [x]
  (some-> x
          class
          ^Class
          (.isArray)))

(s/fdef coll-reduce? :args (s/cat :x any?) :ret boolean?)
(defn coll-reduce? [x]
  (satisfies? clojure.core.protocols/CollReduce x))

(ann/ann #'coll-reduce? (ann/protocol-transformer clojure.core.protocols/CollReduce))

(s/fdef imeta? :args (s/cat :x any?) :ret boolean?)
(def-instance-predicate imeta? clojure.lang.IMeta)
(ann/ann-instance? #'imeta? clojure.lang.IMeta)

(def-instance-predicate ilookup? clojure.lang.ILookup)
(ann/ann-instance? #'imeta? clojure.lang.ILookup)

(def-instance-predicate ref? clojure.lang.IReference)
(ann/ann-instance? #'ref? clojure.lang.IReference)

(def-instance-predicate deref? clojure.lang.IDeref)
(ann/ann-instance? #'deref? clojure.lang.IDeref)

(ann/ann-instance? #'future? java.util.concurrent.Future)

(s/def ::seq-like (s/nilable (s/or :seq seq? :seqable seqable?)))

(def core-predicates [#'associative?
                      #'boolean?
                      #'bigdec?
                      #'coll?
                      #'chunked-seq?
                      #'class?
                      #'double?
                      #'false?
                      #'float?
                      #'fn?
                      #'ifn?
                      #'int?
                      #'integer?
                      #'keyword?
                      #'map?
                      #'number?
                      #'nil?
                      #'qualified-keyword?
                      #'ratio?
                      #'seq?
                      #'sequential?
                      #'set?
                      #'string?
                      #'symbol?
                      #'simple-symbol?
                      #'var?
                      #'vector?])

(s/def ::xf fn?) ;;transducer

(defmacro def-core-predicates []
  (let [calls (map (fn [p]
                     `(predicate-spec ~p)) core-predicates)]
    `(do ~@calls)))

(def-core-predicates)

(s/fdef clojure.core/any? :args (s/cat :x (fn [x] true)) :ret boolean?)
(s/fdef clojure.core/assoc :args (s/cat :m (s/nilable associative?) :pairs (s/+ (s/cat :k any? :v any?))) :ret associative?)
(s/fdef clojure.core/apply :args (s/cat :f ifn? :args (s/* any?) :ret any?))
(s/fdef clojure.core/assoc-in :args (s/cat :m (s/nilable associative?) :ks (s/coll-of any?) :v any?) :ret associative?)
(s/fdef clojure.core/bigdec :args (s/cat :x number?) :ret bigdec?)
(s/fdef clojure.core/cast :args (s/cat :c class? :x any?) :ret any?)
(s/fdef clojure.core/concat :args (s/* ::seq-like) :ret seq?)
(s/fdef clojure.core/commute :args (s/cat :r ref? :f fn? :args (s/* any?)) :ret any?)
(s/fdef clojure.core/conj :args (s/cat :c (s/? (s/nilable coll?)) :x (s/* any?)) :ret coll?)
(s/fdef clojure.core/contains? :args (s/cat :coll (s/alt :nil nil? :a associative? :s set? :m map? :arr array?) :key any?) :ret any?)
(s/fdef clojure.core/deref :args (s/cat :r deref? :ms (s/? pos-int?) :val (s/? any?)))
(s/fdef clojure.core/dissoc :args (s/cat :x (s/nilable map?) :ks (s/* any?)) :ret map?)
(s/fdef clojure.core/doall :args (s/cat :x ::seq-like) :ret seq)
(s/fdef clojure.core/dorun :args (s/cat :x ::seq-like) :ret nil?)
(s/fdef clojure.core/even? :args (s/cat :n integer?) :ret boolean?)
(s/fdef clojure.core/filter :args (s/cat :f any? :coll (s/? ::seq-like)) :ret (s/or :seq seq? :xf ::xf))
(s/fdef clojure.core/first :args (s/cat :coll ::seq-like) :ret any?)
(s/fdef clojure.core/format :args (s/cat :fmt string? :args (s/* any?)) :ret string?)
(s/def ::gettable (s/or :l ilookup? :m map? :s set? :a array? :n nil?))
(s/fdef clojure.core/get :args (s/cat :m ::gettable :k any? :not-found (s/? any?)))
(s/fdef clojure.core/get-in :args (s/cat :m ::gettable :ks (s/coll-of any?) :not-found (s/? any?)))

;; FIXME this breaks all kinds of things
;;(s/fdef clojure.core/hash-map :args (s/* (s/cat :k any? :v any?)) :ret map?)

(s/fdef clojure.core/identity :args (s/cat :x any?) :ret any?)
(s/fdef clojure.core/in-ns :args (s/cat :ns symbol?) :ret namespace?)
(s/fdef clojure.core/inc :args (s/cat :x number?) :ret number?)
(s/fdef clojure.core/instance? :args (s/cat :c class? :x any?) :ret boolean?)
(s/fdef clojure.core/into :args (s/cat :to (s/nilable coll?) :xform (s/? fn?) :from ::seq-like) :ret coll?)
(s/fdef clojure.core/keyword :args (s/or :qualified (s/cat :ns (s/nilable string?) :name string?) :unqualified (s/cat :name any?)) :ret (s/or :k keyword? :n nil?))
(s/fdef clojure.core/list :args (s/* any?) :ret list?)
(s/fdef clojure.core/map :args (s/cat :x ifn? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf ::xf))
(s/fdef clojure.core/map-indexed :args (s/cat :x (s/or :f ifn? :k keyword?) :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf ::xf))
(s/fdef clojure.core/mapcat :args (s/cat :x any? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/mapv :args (s/cat :x any? :coll (s/* ::seq-like)) :ret vector?)
(s/fdef clojure.core/merge :args (s/cat :ms (s/* (s/nilable map?))) :ret map?)
(s/fdef clojure.core/not :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/println :args (s/* any?) :ret nil?)
(s/fdef clojure.core/pr-str :args (s/* any?) :ret string?)
;; (s/fdef clojure.core/push-thread-bindings :args (s/map-of var? any?) :ret nil?)
;; (s/fdef clojure.core/pop-thread-bindings :args (s/cat) :ret nil?)
(s/fdef clojure.core/range :args (s/cat :start (s/? integer?) :end (s/? integer?) :step (s/? integer?)) :ret (s/coll-of integer?))
;; (s/fdef clojure.core/reduce :args (s/cat :f fn? :init-val (s/? any?) :coll (s/nilable (s/coll-of any?))) :ret (s/or  :f fn? :c coll?))

(s/def ::refer-rename (s/cat :r #{:rename} :m (s/map-of symbol? symbol?)))
(s/def ::refer-exclude (s/cat :r #{:exclude} :m (s/coll-of symbol?)))
(s/def ::refer-refer (s/cat :r #{:refer} :m (s/or :all #{:all} :syms (s/coll-of symbol?))))
(s/def ::refer-only (s/cat :r #{:only} :syms (s/coll-of symbol?)))
(s/def ::refer-filter (s/alt :rename ::refer-rename :exclude ::refer-exclude :refer ::refer-refer :only ::refer-only))
(s/fdef clojure.core/refer :args (s/cat :ns symbol? :refer-filters (s/* ::refer-filter)) :ret nil?)

(s/def ::local-name (s/and simple-symbol? #(not= '& %)))
(s/def ::as ::local-name)
(s/def ::refer (s/or :all #{:all} :syms (s/coll-of simple-symbol?)))
(s/def ::prefix-list
  (s/spec
    (s/cat :prefix simple-symbol?
           :suffix (s/* (s/alt :lib simple-symbol? :prefix-list ::prefix-list))
           :refer (s/keys* :opt-un [::as ::refer]))))

(s/fdef clojure.core/require :args (s/* (s/alt :lib simple-symbol?
                                               :prefix-list ::prefix-list
                                               :flag #{:reload :reload-all :verbose})) :ret nil?)
(s/fdef clojure.core/satisfies? :args (s/cat :c protocol? :x any?) :ret boolean?)
(s/fdef clojure.core/select-keys :args (s/cat :m (s/or :m map? :a associative? :_ nil?) :ks (s/coll-of any?)) :ret map?)
(s/fdef clojure.core/seq :args (s/cat :coll ::seq-like) :ret (s/nilable seq?))
(s/fdef clojure.core/seqable? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/sequence :args (s/or :coll (s/cat :c ::seq-like) :xf-coll (s/cat :x ::xf :c ::seq-like) :xf-colls (s/cat :x ::xf :c (s/+ ::seq-like))))
(s/fdef clojure.core/str :args (s/* any?) :ret string?)
(s/fdef clojure.core/vector :args (s/* any?) :ret vector?)
(s/fdef clojure.core/with-meta :args (s/cat :x imeta? :m (s/nilable map?)) :ret imeta?)


(s/fdef clojure.set/union :args (s/* set?) :ret set?)
(predicate-spec clojure.spec.alpha/spec?)
