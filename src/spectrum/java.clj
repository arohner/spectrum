(ns spectrum.java
  (:require [clojure.spec :as s]
            [clojure.set :as set]
            [spectrum.data :as data]))

(def primitive->class- {'long Long
                       Long/TYPE Long
                       'double Double
                       'boolean Boolean
                       Boolean/TYPE Boolean})

(def class->primitive (set/map-invert primitive->class-))

(defn interface? [x]
  (and (class? x) (.isInterface ^Class x)))

(defn primitive? [x]
  (contains? primitive->class- x))

(s/def ::java-type (s/or :p primitive? :c class?))

(s/def ::java-args (s/coll-of ::java-type))

(s/fdef resolve-class :args (s/cat :str symbol?) :ret class?)
(defn resolve-class
  [sym]
  (try
    (clojure.lang.RT/classForName (pr-str sym))
    (catch ClassNotFoundException e
      nil)))

(s/def ::predicate (s/fspec :args (s/cat :x any?) :ret boolean?))

(s/fdef pred->class :args (s/cat :pred ::predicate) :ret (s/nilable Class))
(defn pred->class [pred]
  {:post [(do (when-not % (println "pred->class not found:" pred (class pred))) true)]}
  (get @data/pred->class pred))

(s/fdef primitive->pred :args (s/cat :p primitive?) :ret class?)
(defn primitive->class [p]
  (get primitive->class- p))

(s/fdef shared-ancestors :args (s/cat :a class? :b class?) :ret (s/coll-of class? :into #{}))
(defn shared-ancestors
  "common ancestor other than Object"
  [a b]
  (disj (set/intersection (conj (set (ancestors a)) a)
                          (conj (set (ancestors b)) b))
        Object))

(defn reflect-method? [x]
  (instance? clojure.reflect.Method x))
