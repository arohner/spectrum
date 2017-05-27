(ns spectrum.java
  (:require [clojure.spec :as s]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.data :as data]))

(def primitive->class- {'boolean Boolean
                        'byte Byte
                        'char Character
                        'double Double
                        'float Float
                        'int Integer
                        'long Long
                        'short Short
                        'void Void
                        Boolean/TYPE Boolean
                        Byte/TYPE Byte
                        Character/TYPE Character
                        Double/TYPE Double
                        Float/TYPE Float
                        Integer/TYPE Integer
                        Long/TYPE Long})

(def class->primitive (set/map-invert primitive->class-))

(s/fdef interface? :args (s/cat :x any?) :ret boolean?)
(defn interface? [x]
  (and (class? x) (.isInterface ^Class x)))

(s/fdef primitive? :args (s/cat :x any?) :ret boolean?)
(defn primitive? [x]
  (contains? primitive->class- x))

(s/fdef primitive->class :args (s/cat :p primitive?) :ret class?)
(defn primitive->class [p]
  {:post [%]}
  (get primitive->class- p))

(s/def ::java-type (s/or :p primitive? :c class?))
(s/def ::java-args (s/coll-of ::java-type))

(s/def ::predicate (s/fspec :args (s/cat :x any?) :ret boolean?))

(s/fdef pred->class :args (s/cat :pred ::predicate) :ret (s/nilable Class))
(defn pred->class [pred]
  {:post [(do (when-not % (println "pred->class not found:" pred (class pred))) true)]}
  (get @data/pred->class pred))

(s/fdef shared-ancestors :args (s/cat :a class? :b class?) :ret (s/coll-of class? :into #{}))
(defn shared-ancestors
  "common ancestor other than Object"
  [a b]
  (disj (set/intersection (conj (set (ancestors a)) a)
                          (conj (set (ancestors b)) b))
        Object))

(s/fdef reflect-method? :args (s/cat :x any?) :ret boolean?)
(defn reflect-method? [x]
  (instance? clojure.reflect.Method x))

(defn more-specific?
  [a b]
  (and (isa? a b) (not= a b)))

(defn most-specific-class
  "Given a seq of classes that share an inheritance, return the most specific"
  [cls]
  {:post [(every? (fn [c] (isa? % c)) cls)]}
  (reduce (fn [a b]
            (if (more-specific? a b)
              a
              b)) Object cls))
