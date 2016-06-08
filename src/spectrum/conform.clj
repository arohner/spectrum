(ns spectrum.conform
  (:require [clojure.spec :as s]
            [clojure.set :as set]
            [spectrum.util :refer (fn-literal? literal?)]))

(defprotocol Spect
  (conform* [spec x]
    "True if value x conforms to spec."))

(defprotocol PredConform
  (pred-conform [this pred-s]
    "True if this spec conforms to the pred spec"))

(defprotocol AndConform
  (and-conform [this and-s]
    "True if this spec conforms to the And spec"))

(defprotocol OrConform
  (or-conform [this or-s]
    "True if this spec conforms with the Or spec passed in"))

(defprotocol RegexConform
  (regex-conform [spec seq]
    "True if this seq conforms to the spec"))

(defprotocol Regex
  (derivative
    [spec x]
    "Given a parsed spec, return the derivative")
  (empty-regex [this]
    "The empty pattern for this regex")
  (accept-nil? [this]
    "True if it is valid for this pattern to match no data")
  (return [this]
    "Given a completed regex parse, return the conform matching value"))

(declare accept-regex)
(declare reject-regex)

(declare map->RegexAlt)

(defrecord RegexAccept [ret]
  Regex
  (derivative [spec x]
    reject-regex)
  (empty-regex [spec]
    accept-regex)
  (accept-nil? [this]
    true)
  (return [this]
    ret))

(defn accept [x]
  (map->RegexAccept {:ret x}))

(defrecord RegexReject []
  Regex
  (derivative [spec x]
    nil)
  (empty-regex [spec]
    reject-regex)
  (accept-nil? [this]
    false)
  (return [this]
    ::invalid))

(defn regex-accept? [x]
  (instance? RegexAccept x))

(defn regex-reject? [x]
  (instance? RegexReject x))

(def reject-regex (map->RegexReject {}))

(extend-protocol Regex
  spectrum.conform.Spect
  (derivative [spec x]
    (if (conform* spec x)
      (map->RegexAccept {:ret x})
      reject-regex))
  (empty-regex [this]
    reject-regex)
  (accept-nil? [this]
    false)
  (return [this]
    this))

(extend-protocol Spect
  spectrum.conform.Regex
  (conform* [spec [x & xs :as data]]
    (if (empty? data)
      (if (accept-nil? spec)
        (return spec)
        ::invalid)
      (if-let [dp (derivative spec x)]
        (recur dp xs)
        ::invalid))))

(defn maybe-alt-
  "If both regexes are valid, returns Alt r1 r2, else first non-reject one"
  [r1 r2]
  (if (and r1 r2 (not regex-reject? r1) (not regex-reject? r2))
    (map->RegexAlt {:ps [r1 r2]})
    (first (remove regex-reject? [r1 r2]))))

(declare map->RegexCat)

(defn new-regex-cat [[p0 & pr :as ps] [k0 & kr :as ks] [f0 & fr :as forms] ret]
  (when (every? #(not (regex-reject? %)) ps)
    (if (regex-accept? p0)
      (let [ret (conj ret (if k0 {k0 (:ret p0)} (:ret p0)))]
        (if pr
          (map->RegexCat {:ps pr
                          :ks kr
                          :forms fr
                          :ret ret})
          (accept ret)))

      (map->RegexCat {:ps ps
                      :ks ks
                      :forms forms
                      :ret ret}))))

(defrecord RegexCat [ps ks forms ret]
  Regex
  (derivative [this x]
    (println "cat derivative:" this x)
    (let [[p0 & pr] ps
          [k0 & kr] ks
          [f0 & fr] forms]
      (maybe-alt-
       (new-regex-cat (cons (derivative p0 x) pr) ks forms ret)
       (when (accept-nil? p0)
         (derivative (new-regex-cat pr kr fr ret) x)))))
  (accept-nil? [this]
    (every? accept-nil? ps))
  (return [this]
    ret))

(declare map->RegexSeq)

(defn new-regex-seq [ps ret splice forms]
  (println "new-regex-seq:" ps)
  (when (every? #(not (regex-reject? %)) ps)
    (if (regex-accept? (first ps))
      (map->RegexSeq {:ps (rest ps)
                      :forms forms
                      :ret ((fnil conj []) ret (:ret (first ps)))})
      (map->RegexSeq {:ps ps
                      :forms forms
                      :ret ret}))))

(defrecord RegexSeq [ps ks forms splice ret]
  Regex
  (derivative [this x]
    (println "derivative seq" this x)
    (new-regex-seq [(derivative (first ps) x) (first ps)] ret splice forms))
  (accept-nil? [this]
    true)
  (return [this]
    ret))

(defn filter-alt [ps ks forms f]
  (if (or ks forms)
    (let [pks (->> (map vector ps
                        (or (seq ks) (repeat nil))
                        (or (seq forms) (repeat nil)))
                   (filter #(-> % first f)))]
      [(seq (map first pks)) (when ks (seq (map second pks))) (when forms (seq (map #(nth % 2) pks)))])
    [(seq (filter f ps)) ks forms]))

(defrecord RegexAlt [ps ks forms ret]
  Regex
  (derivative [this x]
    (let [[ps ks forms] (filter-alt (map #(derivative % x) ps) ks forms #(not= % reject-regex))]
      (if (regex-accept? (first ps))
        (map->RegexAccept {:ret [(first ks) (:ret (first ps))]})
        (map->RegexAlt {:ps ps
                        :ks ks
                        :forms forms
                        :ret ret}))))
  (empty-regex [this]
    (map->RegexAlt {:ps (map empty-regex ps)
                    :ks ks
                    :forms forms
                    :ret ret}))
  (accept-nil? [this]
    (some accept-nil? ps))
  (return [this]
    ret))

(declare new-regex-plus)

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
    (literal? x) :literal
    (vector? x) :coll
    (seq? x) (first x)
    :else (throw (Exception. (format "parse-spec unknown: %s" x)))))

(defmulti parse-spec* #'parse-spec-dispatch)

(defmethod parse-spec* :spec-regex [x]
  (parse-regex x))

(defmethod parse-spec* :literal [x]
  x)

(def regex-vars #{'clojure.spec/*})

(defn parse-spec [x]
  (cond
    (s/spec? x) (parse-spec* x)
    (s/regex? x) (parse-spec* x)
    (and (symbol? x) (resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
    (keyword? x) (parse-spec* (#'s/the-spec x))
    (#'s/named? x) (parse-spec* (s/spec x))
    (fn-literal? x) (parse-spec* x)
    (literal? x) x
    (vector? x) (parse-spec* x)
    (and (seq? x) (contains? regex-vars (first x))) (parse-regex x)
    :else (throw (Exception. (format "unknown spec: %s" x)))))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

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

(defmethod parse-spec* :fn-sym [x]
  (let [v (resolve x)]
    (assert v)
    (map->PredSpec {:pred v
                    :form (symbol (str (.ns v)) (str (.sym v)))})))

(defmethod parse-spec* :fn-literal [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* :coll [x]
  (mapv parse-spec* x))

(defmethod parse-spec* 'clojure.core/fn [x]
  (map->PredSpec {:pred (eval x)
                  :form x}))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (first x)))

(defmethod parse-regex :clojure.spec/pcat [x]
  (map->RegexCat {:ks (:ks x)
                  :ps (mapv (fn [[form pred]]
                                          (if (:clojure.spec/op pred)
                                            (parse-regex pred)
                                            (parse-spec form))) (map vector (:forms x) (:ps x)))
                  :forms (:forms x)
                  :ret {}}))

(defn parse-seq [x]
  (let [forms (if (coll? (:forms x))
                (:forms x)
                [(:forms x)])
        preds (mapv parse-spec forms)]
    (map->RegexSeq {:ks (:ks x) :ps preds :forms forms :ret []})))

(defmethod parse-regex :clojure.spec/rep [x]
  (parse-seq x))

(defmethod parse-regex 'clojure.spec/* [x]
  (parse-seq x))

(defmethod parse-regex :clojure.spec/alt [x]
  (map->RegexAlt {:ks (:ks x)
                  :forms (:forms x)
                  :ps (map parse-spec (:forms x))}))

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

(defmethod parse-spec* 'clojure.spec/and [x]
  (map->AndSpec {:forms (mapv (fn [f]
                                (parse-spec f)) (rest x))}))

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

(defmethod parse-spec* 'clojure.spec/or [x]
  (let [pairs (partition 2 (rest x))
        keys (mapv first pairs)
        forms (mapv second pairs)]
    (map->OrSpec {:ks keys
                  :forms (mapv (fn [f]
                                 (parse-spec f)) forms)})))

(defn parse-fn-spec [s]
  (-> s
      (update-in [:args] parse-spec)
      (update-in [:ret] parse-spec)
      (update-in [:fn] parse-spec)))

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
  "Given a spec and args, return the conforming parse. Behaves the same way as s/conform, but args may be clojure literals, or specs, not variables that contain values.

If an arg is a spec, it is treated as a variable that conforms to the spec. pass ::unknown for an variable with no specs.

(conform 'user/defn [symbol? string? [] (+ 1 2)])
=> {:def/name 'user/defn

 "
  [spec args]
  `(let [parsed# (parse-spec ~spec)
         args# (parse-spec ~args)]
     (if-let [val# (conform* parsed# args#)]
       val#
       ::invalid)))
