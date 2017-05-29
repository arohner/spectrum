(ns spectrum.java
  (:require [clojure.spec :as s]
            [clojure.set :as set]
            [clojure.string :as str]
            [spectrum.data :as data]))

(def symbol->primitive- {'boolean Boolean/TYPE
                         'byte Byte/TYPE
                         'char Character/TYPE
                         'double Double/TYPE
                         'float Float/TYPE
                         'int Integer/TYPE
                         'long Long/TYPE
                         'short Short/TYPE
                         'void Void/TYPE})

(def primitives (set (vals symbol->primitive-)))

(def primitive->class- {Boolean/TYPE Boolean
                        Byte/TYPE Byte
                        Character/TYPE Character
                        Double/TYPE Double
                        Float/TYPE Float
                        Integer/TYPE Integer
                        Long/TYPE Long
                        Short/TYPE Short
                        Void/TYPE Void})

(def class->primitive (set/map-invert primitive->class-))

(s/fdef interface? :args (s/cat :x any?) :ret boolean?)
(defn interface? [x]
  (and (class? x) (.isInterface ^Class x)))

(s/fdef primitive? :args (s/cat :x class?) :ret boolean?)
(defn primitive? [x]
  (contains? primitives x))

(s/fdef primitive->class :args (s/cat :p primitive?) :ret class?)
(defn primitive->class [p]
  {:post [%]}
  (get primitive->class- p))

(s/def ::java-args (s/coll-of class?))

(s/fdef resolve-primitive :args (s/cat :x symbol?) :ret (s/nilable class?))
(defn resolve-primitive [x]
  (get symbol->primitive- x))

(defn resolve-java-class-dispatch [x]
  (cond
    (class? x) :class
    (and (symbol? x) (re-find #"<>$" (name x))) :array
    (symbol? x) :symbol

    (string? x) :string
    :else (do (println "resolve-java-class no entry for" x (class x)) (assert false))))

(s/fdef resolve-java-class :args (s/cat :x (s/or :sym symbol? :cls class? :str string?)) :ret class?)
(defmulti resolve-java-class #'resolve-java-class-dispatch)

(defmethod resolve-java-class :symbol [x]
  (let [c (or (resolve-primitive x)
              (clojure.lang.RT/classForName (str x)))]
    (assert (class? c))
    c))

(defmethod resolve-java-class :string [x]
  (resolve-java-class (symbol x)))

(defmethod resolve-java-class :primitive [x]
  x)

(defmethod resolve-java-class :array [x]
  (let [[_ cls] (re-find #"([^<>]+)<>$" (name x))
        cls (resolve-java-class cls)]
    (class (into-array cls []))))

(defmethod resolve-java-class :class [x]
  x)

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
