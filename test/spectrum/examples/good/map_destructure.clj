(ns spectrum.examples.good.map-destructure
  (:require [clojure.spec :as s]))

(s/def ::message string?)

(s/fdef foo :args (s/cat :x (s/keys :req-un [::message])) :ret string?)
(defn foo [{:keys [message]}]
  message)
