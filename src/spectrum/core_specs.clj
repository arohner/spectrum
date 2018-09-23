(ns spectrum.core-specs
  (:require [clojure.core :as core]
            [clojure.spec.alpha :as s]
            [spectrum.ann :as ann]
            [spectrum.core :as st]
            [spectrum.conform :as c]
            [spectrum.util :refer [def-instance-predicate]]))

;;; specs for clojure.core fns, should only be used in cases where
;;; inference can't work, i.e. mostly on things that are built in, but
;;; not defined in clojure source
(def-instance-predicate namespace? clojure.lang.Namespace)

(s/fdef clojure.core/in-ns :args (s/cat :ns symbol?) :ret namespace?)
(s/fdef clojure.core/list :args (s/* any?) :ret list?)

(st/var-spec #'clojure.core/*ns* (c/pred-spec #'namespace?))
(st/var-spec #'clojure.core/*file* (c/pred-spec #'string?))
(st/var-spec #'clojure.core/*print-dup* (c/pred-spec #'boolean?))
(st/var-spec #'clojure.core/*unchecked-math* (c/pred-spec #'boolean?))
(st/var-spec #'clojure.core/*agent* (c/or- [(c/class-spec clojure.lang.Agent) (c/value nil)]))
(st/var-spec #'clojure.core/*warn-on-reflection* (c/pred-spec #'boolean?))

(st/var-spec #'clojure.core/*in* (c/class-spec java.io.Reader))
(st/var-spec #'clojure.core/*out* (c/class-spec java.io.Writer))

(st/var-spec #'clojure.core/*flush-on-newline* (c/pred-spec #'boolean?))
