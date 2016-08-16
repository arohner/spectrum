(ns spectrum.core-specs
  (:require [clojure.core :as core]
            [clojure.spec :as s]
            [spectrum.ann :as ann])
  (:import (java.lang Iterable)
           (java.util Map)
           (clojure.lang ISeq
                         Seqable)))


;;; specs for clojure.core fns, used as hacks/testing. Delete as appropriate

(defn namespace? [x] (instance? clojure.lang.Namespace))

(defn array? [x] (.isArray ^Class (class x)))

(s/fdef reduce? :args (s/cat :x any?) :ret boolean?)
(defn reduce? [x]
  (satisfies? clojure.core.protocols/CollReduce x))

(ann/ann #'reduce? (ann/satisfies-transformer clojure.core.protocols/CollReduce))

(s/def ::seq-like (s/nilable (s/or :seq seq? :seqable seqable?)))

(s/fdef clojure.core/any? :args (s/cat :x (fn [x] (do true))) :ret boolean?)
(s/fdef clojure.core/boolean? :args (s/cat :x #(do % true)) :ret boolean?)
(s/fdef clojure.core/coll? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/concat :args (s/* ::seq-like) :ret seq?)
(s/fdef clojure.core/chunked-seq? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/class? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/dorun :args (s/cat :x ::seq-like) :ret nil?)
(s/fdef clojure.core/doall :args (s/cat :x ::seq-like) :ret seq)
(s/fdef clojure.core/even? :args (s/cat :n integer?) :ret boolean?)
(s/fdef clojure.core/false? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/filter :args (s/cat :x any? :coll (s/? ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/format :args (s/cat :fmt string? :args (s/* any?)) :ret string?)
(s/fdef clojure.core/fn? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/identity :args (s/cat :x any?) :ret any?)
(s/fdef clojure.core/ifn? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/inc :args (s/cat :x number?) :ret number?)
(s/fdef clojure.core/in-ns :args (s/cat :ns symbol?) :ret namespace?)
(s/fdef clojure.core/instance? :args (s/cat :c class? :x any?) :ret boolean?)
(s/fdef clojure.core/into :args (s/cat :to (s/nilable coll?) :xform (s/? fn?) :from reduce?) :ret coll?)
(s/fdef clojure.core/int? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/integer? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/keyword? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/map :args (s/cat :x any? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/map? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/mapcat :args (s/cat :x any? :coll (s/* ::seq-like)) :ret (s/or :seq seq? :xf fn?))
(s/fdef clojure.core/merge :args (s/cat :ms (s/* (s/nilable map?))) :ret map?)
(s/fdef clojure.core/number? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/nil? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/not :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/select-keys :args (s/cat :m (s/or :m map? :a associative? :_ nil?) :ks (s/coll-of any?)) :ret map?)
(s/fdef clojure.core/seq :args (s/cat :coll ::seq-like) :ret (s/nilable seq?))
(s/fdef clojure.core/seq? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/seqable? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/str :args (s/* any?) :ret string?)
(s/fdef clojure.core/string? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/symbol? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/var? :args (s/cat :x any?) :ret boolean?)
(s/fdef clojure.core/vector :args (s/* any?) :ret vector?)
(s/fdef clojure.core/vector? :args (s/cat :x any?) :ret boolean?)
