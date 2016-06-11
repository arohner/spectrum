(ns checker.bad.invoke-non-fn)

(def foo 3)

(defn bar []
  (foo 1))
