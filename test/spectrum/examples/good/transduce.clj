(ns spectrum.examples.good.transduce)

(defn transduce
  "Simplified version of transduce"
  ([xform f coll]
   (transduce xform f (f) coll))
  ([xform f init coll]
   (let [f (xform f)
         ret (clojure.core.protocols/coll-reduce coll f init)]
     (f ret))))
