(ns spectrum.examples.bad.infer-simple)

(defn foo [x]
  (inc x))

(defn run []
  ;; should error here, foo inferred to be [int -> int]
  (foo "hello"))
