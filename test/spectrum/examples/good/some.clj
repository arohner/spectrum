(ns spectrum.examples.good.some
  (:require [clojure.spec :as s]))

(s/fdef foo :args (s/cat ) :ret (s/coll-of integer?))
(defn foo []
  (some->> (range 10)
           (map inc)))
