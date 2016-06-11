(ns checker.bad.static-add)

(defn foo []
  (+ 1 "bogus"))
