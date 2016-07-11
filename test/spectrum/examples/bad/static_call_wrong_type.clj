(ns spectrum.examples.bad.static-call-wrong-type)

(defn foo []
  (clojure.lang.RT/classForName 3))
