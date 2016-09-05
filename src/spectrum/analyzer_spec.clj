(ns spectrum.analyzer-spec
  (:require [clojure.spec :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]))

(s/def ::ana.jvm/op keyword?)
(s/def ::ana.jvm/form any?)

(s/def :ana.jvm.env/file string?)
(s/def :ana.jvm.env/line int?)
(s/def :ana.jvm.env/column int?)
(s/def ::ana.jvm/env (s/keys :req-un [:ana.jvm.env/file :ana.jvm.env/line :ana.jvm.env/column]))

(s/def ::ana.jvm/children (s/coll-of keyword? :into []))

(s/def ::ana.jvm/analysis (s/keys :req-un [::ana.jvm/op ::ana.jvm/form]
                                 :opt-un [::ana.jvm/env
                                          ::ana.jvm/children]))

(defmulti analysis-type :op)

(defmethod analysis-type :default [_]
  ::analysis-common)

(s/def ::ana.jvm/fn ::ana.jvm/analysis)
(s/def ::ana.jvm/args (s/coll-of ::ana.jvm/analysis :into []))

(defmethod analysis-type :invoke [_]
  (s/merge ::analysis-common (s/keys :req-un [::ana.jvm/fn ::ana.jvm/args])))

;;(s/def ::ana.jvm/analysis (s/multi-spec analysis-type :op))

(s/def ::ana.jvm/analyses (s/* ::ana.jvm/analysis))

(s/def ::variadic boolean?)

(s/def ::ana.jvm/binding (s/and ::ana.jvm/analysis #(= (:op %) :binding)))

(s/def ::ana.jvm/bindings (s/coll-of ::ana.jvm/binding))

(s/fdef ana.jvm/analyze-ns :args (s/cat :ns symbol? :env (s/? any?) :opts (s/? any?)) :ret ::ana.jvm/analyses)
