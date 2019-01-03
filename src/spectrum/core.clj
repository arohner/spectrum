(ns spectrum.core
  (:require [clojure.spec.alpha :as s]
            [spectrum.conform :as c]
            [spectrum.java :as j]
            [spectrum.data :as data]
            [spectrum.util :refer [validate!]])
  (:import clojure.lang.Namespace))

(defn var-spec
  "Used to attach a spec to a non-fn var. Checks conformity during binding, set!, alter-var-root, etc."
  [v s]
  {:pre [(validate! var? v)
         (validate! ::c/type s)]}
  (data/store-var-spec v s))
