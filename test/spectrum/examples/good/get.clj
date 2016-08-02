(ns spectrum.examples.good.get
  (:require [clojure.spec :as s]))

;; testing the ann for clojure.core/get

(s/def ::message string?)
(s/fdef basic :args (s/cat :x (s/keys :req-un [::message])) :ret string?)
(defn basic [x]
  (get x :message))

(s/fdef unknown->any :args (s/cat :x (s/keys :req-un [::message])) :ret any?)
(defn unknown->any [x]
  (get x :bogus))
