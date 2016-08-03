(ns spectrum.examples.good.double-recur)

;;  we remove :recur
(defn foo [x]
  (if (pos-int? x)
    (if (even? x)
      (recur (dec x))
      (recur (dec x)))
    x))
