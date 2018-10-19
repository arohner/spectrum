(ns spectrum.java
  (:require [clojure.spec.alpha :as s]
            [clojure.set :as set]
            [clojure.reflect :as reflect]
            [clojure.string :as str]
            [spectrum.data :as data]
            [spectrum.util :refer (predicate-spec)]))

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

(defn final? [x]
  (-> x (reflect/reflect) :flags :final boolean))

(s/fdef array? :args (s/cat :x class?) :ret boolean?)
(defn array? [^Class x]
  (.isArray x))

(defn subclassable?
  "True if it is possible for class X to have child classes"
  [x]
  (not (or
        (primitive? x)
        (array? x)
        (final? x))))

(s/fdef primitive->class :args (s/cat :p primitive?) :ret class?)
(defn primitive->class [p]
  {:post [%]}
  (get primitive->class- p))

(s/fdef maybe-primitive->class :args (s/cat :p class?) :ret class?)
(defn maybe-primitive->class [p]
  (if (primitive? p)
    (primitive->class p)
    p))

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

;;; java overloaded method resolution. You should read the spec first. TL;DR, java uses several rules to determine which arity method gets picked, in order
;;; 1. identity
;;; 2. widening primitive conversion
;;; 3. widening reference (isa?) conversion
;;; 4. boxing + widening
;;;; 5. unboxing + widening


(def widening-primitives
  {Byte/TYPE #{Short/TYPE Integer/TYPE Long/TYPE Float/TYPE Double/TYPE}
   Short/TYPE #{Integer/TYPE Long/TYPE Float/TYPE Double/TYPE}
   Character/TYPE #{Integer/TYPE Long/TYPE Float/TYPE Double/TYPE}
   Integer/TYPE #{Long/TYPE Float/TYPE Double/TYPE}
   Long/TYPE #{Float/TYPE Double/TYPE}
   Float/TYPE #{Double/TYPE}})

(def narrowing-primitives
  {Short/TYPE #{Byte/TYPE Character/TYPE}
   Character/TYPE #{Byte/TYPE Short/TYPE}
   Integer/TYPE #{Byte/TYPE Short/TYPE Character/TYPE}
   Long/TYPE #{Byte/TYPE Short/TYPE Character/TYPE Integer/TYPE}
   Float/TYPE #{Byte/TYPE Short/TYPE Character/TYPE Integer/TYPE Long/TYPE}
   Double/TYPE #{Byte/TYPE Short/TYPE Character/TYPE Integer/TYPE Long/TYPE Float/TYPE}})

(def boxing-conversions
  {Boolean/TYPE Boolean
   Byte/TYPE Byte
   Short/TYPE Short
   Character/TYPE Character
   Integer/TYPE Integer
   Long/TYPE Long
   Float/TYPE Float
   Double/TYPE Double})

(def unboxing-conversions (set/map-invert boxing-conversions))

(s/fdef widening-primitive-conversion? :args (s/cat :a class? :b class?) :ret boolean?)
(defn widening-primitive-conversion?
  "True if casting a -> b is a widening primitive conversion"
  [a b]
  (contains? (get widening-primitives a) b))

(defn widening-reference-conversion?
  "True if casting a -> b is a widening reference conversion"
  [a b]
  (and (isa? a b) (not= a b)))

(def boxed-primitives (set (vals boxing-conversions)))

(predicate-spec boxed?)
(defn boxed?
  "True if x is a boxed primitive"
  [x]
  (boolean (get boxed-primitives x)))

(s/fdef box :args (s/cat :x primitive?) :ret class?)
(defn box [x]
  (get boxing-conversions x))

(s/fdef maybe-box :args (s/cat :x class?) :ret class?)
(defn maybe-box [x]
  (if (primitive? x)
    (box x)
    x))

(s/fdef box :args (s/cat :x class?) :ret primitive?)
(defn unbox [x]
  (or (get unboxing-conversions x)
      (assert false (format "can't unbox %s, not a primitive" x))))

(defn maybe-unbox [x]
  (if (boxed? x)
    (unbox x)
    x))

(defn box-and-widen? [a b]
  (when (primitive? a)
    (let [a* (box a)]
      (or (widening-reference-conversion? a* b)
          (= a* b)))))

(defn unbox-and-widen? [a b]
  (widening-primitive-conversion? (maybe-unbox a) (maybe-unbox b)))

(s/fdef more-specific? :args (s/cat :a class? :b class?) :ret boolean?)
(defn more-specific?
  [a b]
  (or (when (= a b)
        false)
      (when (and (primitive? a) (primitive? b))
        (widening-primitive-conversion? a b))
      (widening-reference-conversion? a b)
      (box-and-widen? a b)
      (unbox-and-widen?  a b)
      false))

(s/fdef primitive-or-boxed? :args (s/cat :x class?) :ret boolean?)
(defn primitive-or-boxed?
  "True if class x is a primitive, or the boxed version of a primitive, i.e. long or Long"
  [x]
  (or (get primitive->class- x)
      (get class->primitive x)))

(s/fdef castable? :args (s/cat :a class? :b class?) :ret boolean?)
(defn castable?
  "True if class a can be implicitly cast to class b"
  [a b]
  (boolean (and (primitive-or-boxed? a) (primitive-or-boxed? b))))

(s/fdef narrowing? :args (s/cat :a class? :b class?) :ret boolean?)
(defn narrowing?
  "True if a can be cast to b, with potential loss of precision"
  [a b]
  (and (not= a b)
       (not= (maybe-unbox a) (maybe-unbox b))
       (castable? a b)
       (not (more-specific? a b))))

(defn most-specific-class
  "Given a seq of classes that share an inheritance, return the most specific"
  [cls]
  {:post [(every? (fn [c] (isa? % c)) cls)]}
  (reduce (fn [a b]
            (if (more-specific? a b)
              a
              b)) Object cls))

(defn get-classloader []
  (-> (java.lang.Thread/currentThread) .getContextClassLoader))

(defn get-byte-code [cls]
  (-> (get-classloader)
      (.getResourceAsStream "clojure/lang/RT.class")
      (slurp)))
