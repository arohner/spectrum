(ns spectrum.examples.good.if
  (:require [clojure.spec :as s]))

(s/fdef if-no-else :args (s/cat :x string?) :ret string?)
(defn no-else [x]
  (if (string? x)
    "truthy"))

(s/fdef ambiguous :args (s/cat :x int?) :ret (s/or :k keyword? :s string?))
(defn ambiguous [x]
  (if (even? x)
    :even
    "odd"))

(s/fdef if-boolean :args (s/cat :x string?) :ret string?)
(defn if-boolean [x]
  (if x
    "truthy"))

(s/fdef booly :args (s/cat :x boolean?) :ret (s/or :k keyword? :s string?))
(defn booly [x]
  (if x
    "then"
    :else))

(s/fdef falsey :args (s/cat :x false?) :ret keyword?)
(defn falsey [x]
  (if (false? x)
    :false))

(s/fdef nil-else :args (s/cat :x nil?) :ret keyword?)
(defn nil-else [x]
  (if (not (nil? x))
    "then"
    :else))

(s/fdef nil-2 :args (s/cat :x nil?) :ret keyword?)
(defn nil-2 [x]
  (if (nil? x)
    :then
    "else"))

(s/fdef falsey-2 :args (s/cat :x any?) :ret keyword?)
(defn falsey-2 [x]
  (if (false? false)
    :false))

(s/def ::a int?)

(s/fdef if-binding :args (s/cat :x (s/keys :req-un [::a])) :ret keyword?)
;; the (seq?) check shouldn't change the type of x during the test, only the branches
(defn if-binding [x]
  (if (seq? x)
    "then"
    :else))

(s/fdef if-binding-2 :args (s/cat :x any?) :ret (s/or :s seq? :_ nil?))
(defn if-binding-2 [x]
  (if (seq? x)
    x))

(s/fdef unknown :ret (s/or :k keyword? :s string?))
(defn unknown [x]
  (if (nil? x)
    :then
    "else"))

(s/fdef class-spec :args (s/cat :x any?) :ret (s/or :k keyword? :s string?))
(defn class-spec [x]
  (if (boolean x)
    :then
    "else"))


;; intentionally unknown fn
(defn unk [x]
  x)

(s/fdef or-unknown :ret (s/or :k keyword? :s string?))
(defn or-unknown []
  (if (->> (unk))
    :then
    "else"))

(s/fdef truthy-pred-nil :args (s/cat :x integer?) :ret string?)
(defn truthy-pred-nil [x]
  (if (nil? x)
    :then
    "else"))

(s/fdef and-truthy :args (s/cat :x (s/and integer? even?)) :ret string?)
(defn and-truthy [x]
  (if (nil? x)
    :then
    "else"))

(s/fdef dependent-preds :args (s/cat :x even?) :ret keyword?)
(defn dependent-preds [x]
  (if (integer? x)
    :then
    "else"))
