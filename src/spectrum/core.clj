(ns spectrum.core
  (:require [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.java :as j])
  (:import clojure.lang.Namespace))

(defn var-spec
  "Used to attach a spec to a non-fn var. Checks conformity during binding, set!, alter-var-root"
  [v s])

;; (defn resolve-class-ns
;;   "Given a local symbol like 'Foo, try resolving it by prepending the ns's name"
;;   [^Namespace ns cls-sym]
;;   (or (j/resolve-class cls-sym)
;;       (inspect (j/resolve-class (inspect (symbol (str (.name ns) "." cls-sym)))))))

;; (s/fdef defrecord-spec :args (s/cat :rec any? :fields any?) :ret any?)
;; (defmacro defrecord-spec
;;   "Takes the defrecord class, and a s/keys spec for the
;;   record. generates specs for ->Record and map->Record. Spec should be
;;   placed in the same namespace, after the defrecord definition has loaded."
;;   [rec fields]
;;   (let [c (eval rec)
;;         positional-name (symbol (str (.name ns) "."))]
;;     )
;;   `(do
;;      (let [c# ~rec]
;;        (println "defrecord-spec class inner" c#)
;;        )

;;      )
;;   )
