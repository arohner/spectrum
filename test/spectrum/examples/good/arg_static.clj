(ns spectrum.examples.good.arg-static)

(defn foo [x]
  (+ x x))

(defn bar [y]
  (foo 1))

(bar 1)
