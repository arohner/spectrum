(ns spectrum.core
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [clojure.set :as set]))

(defn literal? [x]
  (let [a (ana.jvm/analyze x)]
    (and (:literal? a) (not= :unknown (:type a)))))

(defn fn-literal? [x]
  (let [a (ana.jvm/analyze x)]
    (= :fn (:op a))))

(defprotocol Spect
  (conform* [spec x]
    "True if value x conforms to spec"))

(defn parse-regex-dispatch [x]
  (:clojure.spec/op x))

(defmulti parse-regex #'parse-regex-dispatch)

(defn parse-spec-dispatch [x]
  (cond
    (s/spec? x) :spec
    (s/regex? x) :spec-regex
    (symbol? x) :fn-sym
    (var? x) :var
    (fn-literal? x) :fn-literal
    (seq? x) (first x)
    (literal? x) :literal
    :else (throw (Exception. (format "parse-spec unknown: %s" x)))))

(defmulti parse-spec* #'parse-spec-dispatch)

(defmethod parse-spec* :spec-regex [x]
  (parse-regex x))

(defmethod parse-spec* :literal [x]
  x)

(defn parse-spec [x]
  (cond
    (s/spec? x) (parse-spec* x)
    (s/regex? x) (parse-spec* x)
    (and (symbol? x) (resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
    (keyword? x) (parse-spec* (#'s/the-spec x))
    (#'s/named? x) (parse-spec* (s/spec x))
    (fn-literal? x) (parse-spec* x)
    (literal? x) x
    :else (throw (Exception. (format "unknown spec: %s" x)))))

(defprotocol PredConform
  (pred-conform [this pred-s]
    "True if this conforms to pred-s"))

(defprotocol AndConform
  (and-conform [this and-s]
    "True if this conforms to and-s"))

(defprotocol OrConform
  (or-conform [this or-s]
    "True if this conforms to or-s"))

(defrecord PredSpec [pred form]
  Spect
  (conform* [spec x]
    (cond
      (satisfies? PredConform x) (do "x satisfies predconform" (pred-conform x spec))
      (literal? x) (when ((:pred spec) x) x)
      :else false))
  PredConform
  (pred-conform [this pred]
    (when (= (:form this) (:form pred))
      this))
  OrConform
  (or-conform [this or-s]
    (some (fn [[k f]]
            (when (conform* f this)
              [k this])) (map vector (:ks or-s) (:forms or-s)))))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defmethod parse-spec* :fn-sym [x]
  (let [v (resolve x)]
    (assert v)
    (map->PredSpec {:pred v
                    :form (symbol (str (.ns v)) (str (.sym v)))})))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'clojure.core/fn [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (first x)))

(defrecord CatSpec [ks ps forms]
  Spect
  (conform* [this x]
    (assert false "todo")))

(defmethod parse-regex :clojure.spec/pcat [x]
  (map->CatSpec {:ks (:ks x) :ps (mapv (fn [f]
                                         (parse-spec f)) (:forms x)) :forms (:forms x)}))

(defn and-conform-literal [and-s x]
  (when (every? (fn [f]
                  ((:pred f) x)) (:forms and-s))
    x))

(defrecord AndSpec [forms]
  Spect
  (conform* [this x]
    (cond
      (satisfies? AndConform x) (and-conform this x)
      (literal? x) (and-conform-literal this x)))
  PredConform
  (pred-conform [this pred]
    (some (fn [s]
            (conform* pred s)) (:forms this)))
  AndConform
  (and-conform [this that]
    (let [this-specs (set (:forms this))
          that-specs (set (:forms that))]
      (when (= this-specs (set/intersection this-specs that-specs))
        this))))

(defn or-conform-literal [or-s x]
  (some (fn [[k f]]
          (when (conform* f x)
            [k x])) (map vector (:ks or-s) (:forms or-s))))

(defrecord OrSpec [forms]
  Spect
  (conform* [this x]
    (cond
      (satisfies? OrConform x) (or-conform x this)
      (literal? x) (or-conform-literal this x)))

  PredConform
  (pred-conform [this pred]
    (some (fn [s]
            (when (conform* pred s)
              s)) (:forms pred))))

(defmethod parse-spec* 'clojure.spec/and [x]
  (map->AndSpec {:forms (mapv (fn [f]
                                (parse-spec f)) (rest x))}))

(defmethod parse-spec* 'clojure.spec/or [x]
  (let [pairs (partition 2 (rest x))
        keys (mapv first pairs)
        forms (mapv second pairs)]
    (map->OrSpec {:ks keys
                  :forms (mapv (fn [f]
                                 (parse-spec f)) forms)})))

(extend-protocol Spect
  clojure.spec.Spec
  (conform* [spec x]
    (conform* (parse-spec spec) x)))

(extend-type clojure.spec.Spec
  Spect
  (conform* [spec x]
    (conform* (parse-spec* spec) x))
  PredConform
  (pred-conform [spec x]
    (pred-conform (parse-spec spec) x)))

(defmacro conform
  "Given a spec and args, return the conforming parse. Behaves the same way as s/conform, but args may be clojure literals, or specs. If an arg is a spec, it is treated as a variable that conforms to the spec. pass ::unknown for an variable with no specs. In practice, ::unknown will only conform to ::s/any

(conform 'user/defn [symbol? string? [] (+ 1 2)])
=> {:def/name 'user/defn

 "
  [spec args]
  `(let [parsed# (parse-spec ~spec)
         args# (parse-spec ~args)]
     (conform* parsed# args#)))
