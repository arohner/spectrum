(ns spectrum.analyzer-spec
  (:require [clojure.spec :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]))

(s/def ::ana.jvm/op keyword?)
(s/def ::ana.jvm/form any?)
(s/def ::ana.jvm/analysis (s/keys :req-un [:ana.jvm/op :ana.jvm/form]))
(s/def ::ana.jvm/analyses (s/coll-of ::ana.jvm/analysis :into []))
