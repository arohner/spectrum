(ns spectrum.examples.good.map-literal
  (:require [clojure.spec.alpha :as s]))

(s/def ::message string?)

(s/fdef foo :args (s/cat) :ret (s/keys :req-un [::message]))
(defn foo []
  {:message "hello world"})

(s/fdef foo-2 :args (s/cat :x string?) :ret (s/keys :req-un [::message]))
(defn foo-2 [x]
  {:message x})
