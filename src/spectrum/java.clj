(ns spectrum.java
  (:require [clojure.spec :as s]
            [clojure.set :as set]))

(def primitive->class- {'long Long
                       Long/TYPE Long
                       'double Double
                       'boolean Boolean
                       Boolean/TYPE Boolean})

(def class->primitive (set/map-invert primitive->class-))

(defn primitive? [x]
  (contains? primitive->class- x))

(s/def ::java-type (s/or :p primitive? :c class?))

(s/def ::java-args (s/coll-of ::java-type))

(def class->pred- {Double #'double?
                   Integer #'int?
                   java.util.Date #'inst?
                   Number #'number?
                   String #'string?
                   Boolean #'boolean?})


(def pred->class- (set/map-invert class->pred-))

(s/fdef resolve-class :args (s/cat :str symbol?) :ret class?)
(defn resolve-class
  [sym]
  (try
    (clojure.lang.RT/classForName (str sym))
    (catch ClassNotFoundException e
      nil)))

(s/def ::predicate (s/fspec :args (s/cat :x any?) :ret boolean?))

;;(s/fdef pred->class :args (s/cat :pred ::predicate) :ret (s/nilable Class))
(defn pred->class [pred]
  {:post [(do (when-not % (println "pred->class not found:" pred)) true)]}
  (get pred->class- pred))

;;(s/fdef primitive->pred :args (s/cat :p primitive?) :ret class?)
(defn primitive->class [p]
  (get primitive->class- p))

;;(s/fdef shared-ancestors :args (s/cat :a class? :b class?) :ret (s/coll-of class? :into #{}))
(defn shared-ancestors
  "common ancestor other than Object"
  [a b]
  (disj (set/intersection (conj (ancestors a) a)
                          (conj (ancestors b) b))
        Object))

(defn reflect-method? [x]
  (instance? clojure.reflect.Method x))
