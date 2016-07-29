(ns spectrum.examples.good.select-keys
  (:require [clojure.spec :as s]))


(s/def ::foo keyword?)
(s/def ::bar string?)
(s/fdef foo :args (s/cat :x (s/keys :req-un [::foo ::bar])) :ret (s/keys :req-un [::foo]))

(defn foo [x]
  (select-keys x [:foo]))
