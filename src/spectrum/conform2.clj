(ns spectrum.conform2
  (:refer-clojure :exclude [or and not apply isa? vector-of cat * +])
  (:require [clojure.core :as c]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.walk :as walk]
            [spectrum.unify :as u]
            [spectrum.util :refer [instrument-ns]]))

(defn logic-var? [x]
  (c/and (symbol? x)
         (= \? (-> x name first))))

(s/def ::type-atom (s/or :lvar logic-var? :v var? :s symbol? :n nil?))

(s/def ::type (s/or :ta ::type-atom :coll (s/coll-of ::type)))
(s/def ::types (s/coll-of ::type))

(defn unify-distinct
  "unify, but different variables must map to different values"
  [a b]
  (let [a-lvars (u/get-lvars a)
        b-lvars (u/get-lvars b)
        subst (u/unify a b)]
    (when (c/and subst
                 (= (count (distinct (keys subst)))
                    (count (distinct (vals subst)))))
      subst)))

(def conform-patterns (atom {}))

(defn form-node-count [form]
  (let [node-count (atom 0)]
    (walk/postwalk (fn [f]
                     (swap! node-count inc))
                   form)
    @node-count))

(defn def-pattern [state pat f]
  (let [lvars (u/get-lvars pat)
        replace-map (->> lvars
                         (map (fn [l] [l (u/freshen-lvar l)]))
                         (into {}))
        fresh-form (u/rename replace-map pat)]
    (swap! state assoc (with-meta fresh-form {:replace replace-map}) f)))

(defn pattern-invoke [name state args]
  (->> state
       (map (fn [[pat f]]
              (when-let [subst (u/unify pat args)]
                (let [replace-map (-> pat meta :replace)
                      unfresh-map (set/map-invert replace-map)
                      subst* (->> subst
                                  (map (fn [[k v]]
                                         [(get unfresh-map k k) (u/rename unfresh-map v)]))
                                  (into {}))]
                  [pat subst* f]))))
       (filter identity)
       (map (fn [[pat subst f]]
              (f subst)))
       (first)))

(defmacro def-pattern-multi
  "Defines a function multi-method like function, that takes a type pattern, and a fn that is called when the pattern matches. f takes a substitution map"
  [def-name invoke-name]
  `(do
     (let [state# (atom {})]
       (defn ~def-name [pat# f#]
         (def-pattern state# pat# f#))
       (defn ~invoke-name [arg#]
         (pattern-invoke (quote ~invoke-name) @state# arg#)))))

(def-pattern-multi def-accept-nil accept-nil?)
(def-pattern-multi def-conform-strategy find-conform-strategy)

(def types-hierarchy (atom {}))

(defn def-valid
  "define (valid? x y) => true"
  [x y]
  (swap! types-hierarchy update-in [y] (fnil conj #{}) x))

(defn valid* [x y]
  {:post [(do (println "valid*" x y"=>" %) true)]}
  (c/or (= x #'any?)
        (boolean (unify-distinct x y))
        false))

(defn get-ancestors* [t]
  (->> @types-hierarchy
       (mapcat (fn [[y x]]
                 (when-let [subst (u/unify y t)]
                   (u/rename subst x))))
       (filter identity)))

(defn get-ancestors [t]
  (->> (get-ancestors* t)
       (mapcat (fn [t]
                 (concat [t] (get-ancestors t))))
       (distinct)))

(defn valid-ancestor [x y]
  (c/or (valid* x y)
        (->> (get-ancestors y)
             (some #(valid* x %)))))

(defn valid?
  [x y]
  ;;{:post [(do (println "valid?" x y "=>" %) true)]}
  (let [result (valid-ancestor x y)]
    (if result
      result
      (if-let [result (find-conform-strategy [x y])]
        result
        false))))

(s/fdef match :args (s/cat :v var? :args (s/coll-of ::type) :ret ::type))
(defn match
  "Pattern match. Given the var to a function with polymorphic behavior, enhance the function's spec."
  [f args ret])

(defn apply
  "Given a type, apply with args. Return the return type. Uses pattern matches if available. If no patterns availabe, use the spec"
  [t args])

(defn or? [x]
  (c/and (vector? x)
         (= 'or) (first x)))

(defn or-types [o]
  (nth o 1))

(defn or-rest
  "Given an or type, return an or type with the `rest` of the types"
  [ors]
  (or (rest (or-types ors))))

(defn or [& ts]
  (cond
    (>= (count ts) 2) ['or (set ts)]
    (= 1 (count ts)) (first ts)
    :else nil))

(defn and [& ts]
  (cond
    (>= (count ts) 2) ['and (set ts)]
    (= 1 (count ts)) (first ts)
    :else nil))

(defn and? [x]
  (c/and (vector? x)
         (= 'and) (first x)))

(defn and-types [a]
  (nth a 1))

(defn and-rest [a]
  (c/and (rest (and-types a))))

(s/fdef seq-of :args (s/cat :t ::type) :ret ::type)
(defn seq-of [x]
  ['seq-of x])

(s/fdef cat :args (s/cat :t (s/nilable ::types)) :ret ::type)
(defn cat [ps]
  (c/apply vector 'cat ps))

(s/fdef alt :args (s/cat :t (s/nilable ::types)) :ret (s/nilable ::type))
(defn alt [ps]
  (when (seq ps)
    (c/apply vector 'alt ps)))

(defn accept [x]
  ['accept x])

(defn accept? [x]
  (= 'accept (first x)))

(defn ? [x]
  (alt [x nil]))

(defn * [x]
  (seq-of x))

(defn + [x]
  (cat [x (* x)]))

(defn coll-of [x]
  ['coll-of x])

(defn map-entry [x y]
  ['map-entry x y])

(defn vector-of [x]
  ['vector-of x])

(defn nilable [x]
  (or #'nil? x))

(defn value [x]
  ['value x])

(def-pattern-multi def-derivative dx)

(def-conform-strategy '[[or ?x] ?y] (fn [{:syms [?x ?y]}]
                                      (valid? (u/contains ?x) ?y)))

;; (def-conform-strategy ['or (u/contains #{'?x})] '?x true)

(def-conform-strategy '[?x [and ?y]] (fn [{:syms [?x ?y]}]
                                       (valid? ?x (u/contains ?y))))

;; (def-conform-strategy ['or '?x] ['and '?y] (fn [?x ?y]
;;                                              (->>
;;                                               ?y
;;                                               (some (fn [y]
;;                                                       (valid? []))))

;;                                              ))

;; (def-conform-strategy ['and '?x] ['or '?y] (fn [x y]
;;                                              ;; (if (and? y)
;;                                              ;; (valid? x (u/contains (and-types y)))
;;                                              ;; false)
;;                                              ))

(def-conform-strategy '[[and ?x] [and ?y]] (fn [{:syms [?x ?y]}]
                                             (->> ?x
                                                  (some (fn [x]
                                                          (valid? x (and ?y)))))))

(def-conform-strategy '[[or ?x] [or ?y]] (fn [{:syms [?x ?y]}]
                                           (->> ?y
                                                (every? (fn [y]
                                                          (valid? (or ?x) y))))))

(def-pattern-multi def-regex regex?)

(def-regex '[cat ?x] (constantly true))
(def-regex '[seq-of ?x] (constantly true))
(def-regex '[alt ?x] (constantly true))

(def-derivative '[[cat ?x & ?xs] ?y]
  (fn [{:syms [?x ?xs ?y] :as args}]
    {:post [(do (println "cat dx" (cat (concat [?x] ?xs)) ?y "=>" %) true)]}
    (cond
      (regex? ?x) (let [ret (dx [?x ?y])]
                    (cond
                      (accept? ret) (cat ?xs)
                      ret (cat (concat [ret] ?xs))
                      (accept-nil? ?x) (dx [(cat ?xs) ?y])))
      (valid? ?x ?y) (cat ?xs))))

(def-derivative '[[seq-of ?x] ?y]
  (fn [{:syms [?x ?y] :as args}]
    {:post [(do (println "seq dx" args "=>" %) true)]}
    (when (valid? ?x ?y)
      (seq-of ?x))))

(def-derivative '[[alt & ?xs] ?y]
  (fn [{:syms [?xs ?y]}]
    {:post [(do (println "alt dx" ?xs ?y "=>" %) true)]}
    (->> ?xs
         (map (fn [?x]
                (when (valid? ?x ?y)
                  (accept ?x))))
         (filter identity)
         first)))

(def-conform-strategy '[[cat & ?xs] [cat & ?ys]] (fn [{:syms [?xs ?ys]}]
                                                   {:pre [(do (println "cat-cat:" (cat ?xs) (cat ?ys)) true)]
                                                    :post [(do (println "cat-cat:" (cat ?xs) (cat ?ys) "=>" %) true)]}
                                                   (let [?x (first ?xs)
                                                         ?y (first ?ys)]
                                                     (println "cat-cat dx" ?xs ?y)
                                                     (when-let [ret (dx [(cat ?xs) ?y])]
                                                       (valid? ret (cat (rest ?ys)))))))

(def-conform-strategy '[[seq-of ?x] [cat & ?ys]] (fn [{:syms [?x ?ys]}]
                                                   (let [?y (first ?ys)]
                                                     (c/or
                                                      (c/and (valid? ?x ?y)
                                                             (valid? (seq-of ?x) (cat (rest ?ys))))
                                                      (nil? ?ys)))))

(def-conform-strategy '[[cat ?x & ?xs] [seq-of ?y]] (fn [{:syms [?x ?xs ?y]}]
                                                      (c/and (valid? ?x ?y)
                                                             (valid? (cat ?xs) (seq-of ?y)))))

(def-conform-strategy '[[alt ?x & ?xs] ?y] (fn [{:syms [?x ?xs ?y] :as subst}]
                                             (c/or (valid? ?x ?y)
                                                   (valid? (alt ?xs) ?y)
                                                   (when (and (nil? ?x) (nil? ?xs))
                                                     true))))

(def-accept-nil '[alt & ?xs] (fn [{:syms [?xs] :as subst}]
                               (some nil? ?xs)))

(def-accept-nil '[seq-of ?x] (fn [t]
                               true))

(def-accept-nil '[cat & ?xs] (fn [{:syms [?xs]}]
                               (every? accept-nil? ?xs)))

(def-valid #'number? #'integer?)
(def-valid #'number? #'double?)
(def-valid #'integer? #'int?)
(def-valid #'int? #'even?)
(def-valid #'seqable? (seq-of '?x))
(def-valid #'seqable? (coll-of '?x))

(def-valid (coll-of '?x) (vector-of '?x))

(instrument-ns)
