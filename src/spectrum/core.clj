(ns spectrum.core
  (:require [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.java :as j])
  (:import clojure.lang.Namespace))

(defn var-spec
  "Used to attach a spec to a non-fn var. Checks conformity during binding, set!, alter-var-root"
  [v s])

(defn defrecord-spec
  "Attach a spec to a defrecord. You probably want to use s/keys"
  [r s])
