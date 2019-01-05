(ns spectrum.core-specs
  (:require [clojure.core :as core]
            [clojure.spec.alpha :as s]
            [spectrum.core :as st]
            [spectrum.types :as t]
            [spectrum.util :refer [def-instance-predicate]]))

;;; specs for clojure.core fns, should only be used in cases where
;;; inference can't work, i.e. mostly on things that are built in,
;;; i.e. not defined in clojure source.
(def-instance-predicate namespace? clojure.lang.Namespace)

(s/fdef clojure.core/in-ns :args (s/cat :ns symbol?) :ret namespace?)
(s/fdef clojure.core/list :args (s/* any?) :ret list?)

(st/var-spec #'clojure.core/*ns* #'namespace?)
(st/var-spec #'clojure.core/*file* #'string?)
(st/var-spec #'clojure.core/*print-dup* #'boolean?)
(st/var-spec #'clojure.core/*unchecked-math* #'boolean?)
(st/var-spec #'clojure.core/*agent* (t/or-t [(t/class-t clojure.lang.Agent) (t/value-t nil)]))
(st/var-spec #'clojure.core/*warn-on-reflection* #'boolean?)

(st/var-spec #'clojure.core/*in* (t/class-t java.io.Reader))
(st/var-spec #'clojure.core/*out* (t/class-t java.io.Writer))
(st/var-spec #'clojure.core/*err* (t/class-t java.io.Writer))

(st/var-spec #'clojure.core/*flush-on-newline* #'boolean?)
