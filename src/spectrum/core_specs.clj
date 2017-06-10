(ns spectrum.core-specs
  (:require [clojure.core :as core]
            [clojure.spec :as s]
            [spectrum.ann :as ann]
            [spectrum.util :refer (protocol? predicate-spec)])
  (:import (java.lang Iterable)
           (java.util Map)
           (clojure.lang ISeq
                         Seqable)))


;;; specs for clojure.core fns, used as hacks/testing. Delete when official versions become available

(defn namespace? [x] (instance? clojure.lang.Namespace))

(defn array? [x] (.isArray ^Class (class x)))

(s/fdef coll-reduce? :args (s/cat :x any?) :ret boolean?)
(defn coll-reduce? [x]
  (satisfies? clojure.core.protocols/CollReduce x))

(ann/ann #'coll-reduce? (ann/protocol-transformer clojure.core.protocols/CollReduce))

(s/fdef imeta? :args (s/cat :x any?) :ret boolean?)
(defn imeta? [x]
  (instance? clojure.lang.IMeta x))

(ann/ann-instance? #'imeta? clojure.lang.IMeta)

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
                      #'ratio?
                      #'seq?
                      #'set?
                      #'string?
                      #'symbol?
                      #'var?
                      #'vector?])

(defmacro def-core-predicates []
  (let [calls (map (fn [p]
                     `(predicate-spec ~p)) core-predicates)]
    `(do ~@calls)))

(def-core-predicates)

(s/fdef clojure.core/any? :args (s/cat :x (fn [x] true)) :ret boolean?)
(s/fdef clojure.core/bigdec :args (s/cat :x number?) :ret bigdec?)
(s/fdef clojure.core/concat :args (s/* ::seq-like) :ret seq?)
(s/fdef clojure.core/dissoc :args (s/cat :x (s/nilable map?) :ks (s/* any?)) :ret map?)
(s/fdef clojure.core/dorun :args (s/cat :x ::seq-like) :ret nil?)
(s/fdef clojure.core/doall :args (s/cat :x ::seq-like) :ret seq)
(s/fdef clojure.core/even? :args (s/cat :n integer?) :ret boolean?)
(s/fdef clojure.core/first :args (s/cat :coll ::seq-like) :ret any?)
(s/fdef clojure.core/filter :args (s/cat :f any? :coll (s/? ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/format :args (s/cat :fmt string? :args (s/* any?)) :ret string?)
(s/fdef clojure.core/identity :args (s/cat :x any?) :ret any?)
(s/fdef clojure.core/inc :args (s/cat :x number?) :ret number?)
(s/fdef clojure.core/in-ns :args (s/cat :ns symbol?) :ret namespace?)
(s/fdef clojure.core/instance? :args (s/cat :c class? :x any?) :ret boolean?)
(s/fdef clojure.core/into :args (s/cat :to (s/nilable coll?) :xform (s/? fn?) :from ::seq-like) :ret coll?)

;; TODO keyword needs case. returns nil only when passed something other than string symbol keyword
(s/fdef clojure.core/keyword :args (s/or :qualified (s/cat :ns (s/nilable string?) :name string?) :unqualified (s/cat :name any?)) :ret (s/or :k keyword? :n nil?))
(s/fdef clojure.core/map :args (s/cat :x any? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/mapv :args (s/cat :x any? :coll (s/* ::seq-like)) :ret vector?)
(s/fdef clojure.core/mapcat :args (s/cat :x any? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/merge :args (s/cat :ms (s/* (s/nilable map?))) :ret map?)
(s/fdef clojure.core/println :args (s/* any?) :ret nil?)
(s/fdef clojure.core/not :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/range :args (s/cat :start (s/? integer?) :end (s/? integer?) :step (s/? integer?)) :ret (s/coll-of integer?))
(s/fdef clojure.core/satisfies? :args (s/cat :c protocol? :x any?) :ret boolean?)
(s/fdef clojure.core/select-keys :args (s/cat :m (s/or :m map? :a associative? :_ nil?) :ks (s/coll-of any?)) :ret map?)
(s/fdef clojure.core/seq :args (s/cat :coll ::seq-like) :ret (s/nilable seq?))
(s/fdef clojure.core/seqable? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/str :args (s/* any?) :ret string?)


(s/fdef clojure.core/vector :args (s/* any?) :ret vector?)

(s/fdef clojure.core/with-meta :args (s/cat :x imeta? :m (s/nilable map?)) :ret imeta?)

(predicate-spec clojure.spec/spec?)

;;; core annotations
