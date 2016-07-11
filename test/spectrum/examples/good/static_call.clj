(ns spectrum.examples.good.static-call)

(defn foo []
  (clojure.lang.RT/classForName "java.lang.String"))
