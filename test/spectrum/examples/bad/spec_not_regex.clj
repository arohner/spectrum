(ns spectrum.examples.bad.spec-not-regex
  (:require [clojure.spec :as s]))

;; args spec isn't a regex
(s/fdef foo :args int? :ret int?)

(defn foo [x]
  (inc x))
