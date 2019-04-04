(ns spectrum.parse-spec
  (:require [clojure.core.memoize :as memo]
            [clojure.spec.alpha :as s]
            [spectrum.types :as t]
            [spectrum.flow :as f]
            [spectrum.util :refer [multimethod-dispatch-values var-name]])
  (:import [clojure.lang Var]))

(defn form? [x]
  (and (sequential? x)
       (seq? x)
       (symbol? (first x))))

(defn macro? [v]
  (and (var? v) (.isMacro ^Var v)))

(declare can-parse?)

(defn known-form? [x]
  (let [sym (first x)
        v (resolve sym)]
    (and (seq? x) (symbol? (first x)) (var? v) (can-parse? sym))))

(defn fn-literal? [x]
  (and (form? x)
       (or (= 'fn (first x))
           (= 'fn* (first x)))))

(defn parse-spec*-dispatch [x]
  {:post [(do (when (nil? %)
                (println "don't know how to parse" x))
              true)

          %]}
  (cond
    (s/spec? x) :spec
    (s/regex? x) (::s/op x)
    (t/logic? x) :literal
    (and (form? x) (known-form? x)) (first x)
    (and (form? x) (not (known-form? x)) (macro? (resolve (first x)))) :macro
    (symbol? x) :sym
    (var? x) :var
    (fn-literal? x) :fn-literal
    (keyword? x) :keyword
    (set? x) :set
    (coll? x) :coll
    (class? x) :class
    :else :literal))

(defmulti parse-spec* #'parse-spec*-dispatch)

(defn can-parse? [x]
  (contains? (set (multimethod-dispatch-values parse-spec*)) x))

(defmethod parse-spec* :literal [x]
  (if (t/type? x)
    x
    (t/value-t x)))

(defmethod parse-spec* :class [x]
  {:pre [(class? x)]}
  (t/class-t x))

(defn maybe-resolve [x]
  (try
    (resolve x)
    (catch Exception e
      nil)))

(defn spec-registry?
  "true if keyword x was s/def'd"
  [x]
  (#'clojure.spec.alpha/maybe-spec x))

(defn parse-spec- [x]
  {:post [%]}
  (try
    (cond
      (t/logic? x) x
      (and (symbol? x) (maybe-resolve x)) (parse-spec* (s/spec-impl x (resolve x) nil nil))
      (var? x) (parse-spec* (s/spec-impl (var-name x) x nil nil))
      (= ::s/nil x) nil
      (spec-registry? x) (parse-spec* (s/form (s/spec x)))
      (s/spec? x) (parse-spec* (s/form x))
      (s/regex? x) (parse-spec* x)
      :else (parse-spec* x))
    (catch IllegalArgumentException e
      (println "don't know how to parse:" x)
      (throw e))))

(def parse-spec (memo/memo parse-spec-))

(defmethod parse-spec* :keyword [x]
  (if (and (qualified-keyword? x) (s/get-spec x))
    (parse-spec (s/get-spec x))
    (t/value-t x)))

(defmethod parse-spec* :macro [x]
  (let [v (resolve (first x))
        args (rest x)
        form (apply v nil nil args)]
    (parse-spec* form)))

(defmethod parse-spec* :sym [x]
  (let [v (resolve x)]
    (if v
      (cond
        (var? v) v
        (class? v) (t/class-t v)
        :else (assert false (format "unknown: %s" x)))
      (t/value-t x))))

(defmethod parse-spec* :spec [x]
  (parse-spec* (s/form x)))

(defmethod parse-spec* :fn-literal [x]
  (assert false "TODO"))

(def any?-form '(clojure.core/fn [x] true))
(def any?-macroexpanded '(fn* ([x] true)))

(defmethod parse-spec* 'clojure.core/fn [x]
  (if (= x any?-form)
    #'any?
    (-> x f/infer-form)))

(defmethod parse-spec* 'fn* [x]
  (if (= x any?-form)
    #'any?
    (assert false "TODO")))

(defmethod parse-spec* 'quote [x]
  (parse-spec* (second x)))

(defmethod parse-spec* 'var [x]
  (parse-spec* (second x)))

(defmethod parse-spec* `s/spec [x]
  (t/spec-t (parse-spec* (second x))))

(defn unquote-form
  "Given a '(quote foo), return 'foo"
  [f]
  (first (rest f)))

(defmethod parse-spec* `s/spec-impl [x]
  (let [[form pred & _ ] (rest x)]
    (t/spec-t (unquote-form form))))

(defmethod parse-spec* ::s/pcat [x]
  (assert false (format "parse s/pcat %s" x))
  (t/cat-t []))

(defmethod parse-spec* ::s/accept [x]
  nil)

(defmethod parse-spec* `s/cat [x]
  (let [pairs (->> x rest (partition 2))
        ks (map first pairs)
        ps (map second pairs)]
    (t/cat-t (map parse-spec* ps))))

(defmethod parse-spec* `s/cat-impl [x]
  (let [[ks ps forms] (rest x)
        forms (unquote-form forms)]
    (t/cat-t ps)))

;; (defmethod parse-spec* ::s/rep [x]
;;   (let [forms (if (vector? (:forms x))
;;                 (:forms x)
;;                 [(:forms x)])]
;;     (assert (= 1 (count forms)))
;;     (seq- (first forms) {:splice (:splice x)})))

;; (defmethod parse-spec* `s/rep-impl [x]
;;   (let [[form pred] (rest x)
;;         form (unquote-form form)]
;;     (seq- form {:splice false})))

(defmethod parse-spec* `s/+ [x]
  (let [forms (rest x)
        p (first forms)
        p (parse-spec* p)]
    (assert (= 1 (count forms)))
    (t/cat-t [p (t/seq-of p)])))

;; (defmethod parse-spec* `s/rep+impl [x]
;;   (let [[form pred] (rest x)
;;         form (unquote-form form)]
;;     (p/map->RegexCat {:forms [form]
;;                       :ps [form (seq- form {:splice true})]
;;                       :ret []})))

(defmethod parse-spec* `s/* [x]
  (let [forms (rest x)
        s (first forms)]
    (assert (= 1 (count forms)))
    (t/seq-of (parse-spec* s))))

(defmethod parse-spec* ::s/alt [x]
  (t/alt-t (map parse-spec (:forms x))))

(defmethod parse-spec* `s/? [x]
  (t/alt-t [(-> x second parse-spec*) nil]))

;; (defmethod parse-spec* `s/alt [x]
;;   (let [pairs (partition 2 (rest x))
;;         ks (mapv first pairs)
;;         forms (mapv second pairs)]
;;     (p/map->RegexAlt {:ks ks
;;                       :forms forms
;;                       :ps forms})))

;; (defmethod parse-spec* `s/alt-impl [x]
;;   (let [[ks ps forms] (rest x)]
;;     (p/map->RegexAlt {:ks ks
;;                       :forms forms
;;                       :ps (unquote-form forms)})))

;; (defmethod parse-spec* `s/maybe-impl [x]
;;   (let [[pred form] (rest x)
;;         form (unquote-form form)]
;;     (p/map->RegexAlt {:ps [form (accept nil)]})))

;; (defmethod parse-spec* :clojure.spec.alpha/amp [x]
;;   (unknown {:message (format "TODO don't know how to handle %s" x)}))

;; (defmethod parse-spec* `s/amp-impl [x]
;;   (unknown {:message (format "TODO don't know how to handle %s" x)}))

(defmethod parse-spec* `s/and [x]
  (t/and-t (->> x rest (map parse-spec))))

;; (defmethod parse-spec* `s/and-spec-impl [x]
;;   (let [[forms preds gen-fn] (rest x)
;;         ps (unquote-form forms)]
;;     (and- ps)))

;; (defmethod parse-spec* `s/or [x]
;;   (let [pairs (map vec (partition 2 (rest x)))
;;         ks (map first pairs)
;;         ps (map second pairs)]
;;     (or- ps)))

;; (defmethod parse-spec* `s/or-spec-impl [x]
;;   (let [[ks forms ps gen-fn] (rest x)
;;         forms (unquote-form forms)]
;;     (or- forms)))

(defmethod parse-spec* `s/tuple [x]
  (let [preds (rest x)]
    (t/cat-t (map parse-spec (rest x)))))

;; (defmethod parse-spec* `s/tuple-impl [x]
;;   (let [[forms preds] (rest x)]
;;     (p/map->TupleSpec {:ps (unquote-form forms)})))

;; (s/fdef array-of :args (s/cat :x class-spec?) :ret ::spect)
;; (defn array-of [p]
;;   (p/map->ArrayOf {:p p}))

;; (defmethod parse-spec* `s/nilable [x]
;;   (let [s (second x)]
;;     (or- [(parse-spec s) (parse-spec #'nil?)])))

;; (defmethod parse-spec* `s/nilable-impl [x]
;;   (let [[form pred gen-fn] (rest x)
;;         form (unquote-form form)]
;;     (or- [form (pred-spec #'nil?)])))

;; (defmethod parse-spec* `s/or [x]
;;   (let [pairs (partition 2 (rest x))
;;         keys (mapv first pairs)
;;         forms (mapv second pairs)]
;;     (or- forms)))

;; (defmethod parse-spec* `s/keys [x]
;;   (let [args (->> (rest x)
;;                   (partition 2)
;;                   (map (fn [[key-type specs]]
;;                          [key-type (into {} (map (fn [spec-name]
;;                                                    (if-let [s (s/get-spec spec-name)]
;;                                                      [spec-name (s/form s)]
;;                                                      (throw (Exception. (format "Could not resolve spec: %s" spec-name))))) specs))]))
;;                   (into {} ))]
;;     (keys-spec (:req args)
;;                (:req-un args)
;;                (:opt args)
;;                (:opt-un args))))

;; (defmethod parse-spec* `s/map-spec-impl [x]
;;   (let [args (first (rest x))]
;;     (let [parse-keys (fn [ks]
;;                        (into {} (map (fn [k]
;;                                        [k k]) ks)))]
;;       (keys-spec (parse-keys (unquote-form (:req args)))
;;                  (parse-keys (unquote-form (:req-un args)))
;;                  (parse-keys (unquote-form (:opt args)))
;;                  (parse-keys (unquote-form (:opt-un args)))))))

(defn parse-spec-seq [x]
  (let [v (mapv parse-spec* x)]
    (if (list? x)
      (t/value-t (list* v))
      (t/value-t (into (or (empty x) []) v)))))

;; (defn parse-spec-map [x]
;;   (let [state (reduce (fn [state [k v]]
;;                         (cond
;;                           (qualified-keyword? k) (assoc-in state [:req k] (parse-spec v))
;;                           (simple-keyword? k) (assoc-in state [:req-un k] (parse-spec v)))) {:req {}
;;                                                                                              :req-un {}} x)]
;;     (keys-spec (:req state) (:req-un state) {} {})))

(defmethod parse-spec* :set [x]
  (t/or-t (mapv parse-spec x)))

(defmethod parse-spec* :coll [x]
  (cond
    (sequential? x) (parse-spec-seq x)
    ;; (map? x) (parse-spec-map x))
  ))

;; (defmethod parse-spec* `s/every [x]
;;   (parse-coll-of x))

;; (defmethod parse-spec* `s/every-impl [x]
;;   (let [[form pred opts] (rest x)
;;         form (unquote-form form)
;;         s (parse-spec form)
;;         empty-kind (get kind->coll (get opts :kind))]
;;     (if (= 'clojure.core/map? (:kind opts))
;;       (parse-map-of x)
;;       (p/map->CollOfSpec (merge {:s s
;;                                  :empty-kind empty-kind} opts)))))

;; (defmethod parse-spec* `s/coll-of [x]
;;   (parse-coll-of x))

;; (defmethod parse-spec* `s/map-of [x]
;;   (let [k (nth x 1)
;;         v (nth x 2)]
;;     (map-of k v)))

;; (defmethod parse-spec* `s/merge [x]
;;   (apply merge-specs (rest x)))

;; (defmethod parse-spec* `s/merge-spec-impl [x]
;;   (let [[forms preds & _] (rest x)
;;         forms (unquote-form forms)]
;;     (apply merge-specs forms)))

;; (defmethod parse-spec* `s/conformer [x]
;;   (value true))

;; (defmethod parse-spec* `s/nonconforming [x]
;;   (parse-spec* (second x)))

;; (defmethod parse-spec* `s/fspec [x]
;;   (let [pairs (->> x rest (partition 2))
;;         pairs (map (fn [[k p]]
;;                      (when p
;;                        [k (parse-spec p)])) pairs)
;;         args (into {} pairs)]
;;     (p/map->FnSpec args)))

;; (defmethod parse-spec* `s/fspec-impl [x]
;;   (let [[arg-spec arg-form ret-spec ret-form fn-spec fn-form gen-fn] (rest x)
;;         args (unquote-form arg-form)
;;         ret (unquote-form ret-form)
;;         fn (unquote-form fn-form)
;;         args (when args
;;                (parse-spec args))
;;         ret (when ret
;;               (parse-spec ret))
;;         fn (when fn
;;              (parse-spec fn))]
;;     (p/map->FnSpec (merge (when arg-spec
;;                             {:args args})
;;                           (when ret-spec
;;                             {:ret ret})
;;                           (when fn-spec
;;                             {:fn fn})))))

;; (defmethod parse-spec* `s/multi-spec [x]
;;   (let [retag (nth x 2)
;;         retag (cond
;;                 (keyword? retag) retag
;;                 (symbol? retag) (resolve retag))
;;         method (resolve (nth x 1))]
;;     (assert retag)
;;     (multispec method retag)))

;; (defmethod parse-spec* `s/multi-spec-impl [x]
;;   (let [[form mmvar-form retag] (rest x)
;;         mmvar (resolve (second mmvar-form))]
;;     (assert (var? mmvar))
;;     (multispec-default-spec (multispec mmvar retag))))
