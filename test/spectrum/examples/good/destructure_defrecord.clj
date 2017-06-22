(ns spectrum.examples.good.destructure-defrecord
  (:require [clojure.spec.alpha :as s]
            [spectrum.ann :as ann]))

(s/def ::a integer?)
(s/def ::b string?)

(defrecord Foo [a b])

(s/fdef foo? :args (s/cat :x any?) :ret boolean?)
(defn foo? [x]
  (instance? Foo x))

(s/fdef map->Foo :args (s/cat :x (s/keys :req-un [::a ::b])) :ret foo?)

(ann/ann #'foo? (ann/instance-transformer Foo))

(s/fdef new-foo :args (s/cat :args (s/keys :req-un [::a ::b])) :ret foo?)
(defn new-foo [{:keys [a b] :as args}]
  (map->Foo args))
