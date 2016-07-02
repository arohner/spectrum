(ns spectrum.examples.bad.arity)

(defn foo
  ([]
   nil)
  ([x]
   x))

(defn bar []
  (foo 1 2))
