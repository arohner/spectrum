(ns spectrum.queue)

(defn q
  ([]
   (clojure.lang.PersistentQueue/EMPTY))
  ([coll]
   (into (q) coll)))

(defn queue? [x]
  (instance? clojure.lang.PersistentQueue x))

(defmethod print-method clojure.lang.PersistentQueue
  [q ^java.io.Writer w]
  (.write w "#queue ")
  (print-method (sequence q) w))
