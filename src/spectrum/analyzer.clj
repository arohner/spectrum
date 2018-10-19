;;   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns spectrum.analyzer
  "Analyzer for clojure code, extends tools.analyzer with JVM specific passes/forms"
  (:require [clojure.spec.alpha :as s]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.tools.analyzer.jvm.utils :as utils]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.reader :as reader]
            [clojure.tools.reader.reader-types :as readers]
            [clojure.java.io :as io]
            [spectrum.util :refer [url? instrument-ns]])
  (:import (clojure.lang IObj RT Compiler Var)
           java.net.URL))

(defn form-predicate
  "Returns a predicate checking if the form calls a symbol `sym`"
  [sym]
  (fn [form]
    (and (sequential? form) (-> form first (= sym)))))

(def form-ns? (form-predicate 'ns))
(def form-in-ns? (form-predicate 'in-ns))

(defn should-eval-form? [form]
  {:post [(do (when % (println "evaling" form)) true)]}
  (or (form-ns? form)
      (form-in-ns? form)))

(defn analyze-file-
  "ana.jvm/analyze a file, but only eval the `ns` form, and non-eval analyze all others"
  [env res filename opts]
  (with-open [rdr (io/reader res)]
    (let [path     (.getPath res)
          pbr (readers/indexing-push-back-reader
               (java.io.PushbackReader. rdr) 1 filename)
          eof (Object.)
          read-opts {:eof eof :features #{:clj :t.a.jvm}}
          read-opts (if (.endsWith filename "cljc")
                      (assoc read-opts :read-cond :allow)
                      read-opts)]
      (loop [first-form? true]
        (let [form (reader/read read-opts pbr)]
          (when-not (identical? form eof)
            (swap! env/*env* update-in [::analyzed-clj path]
                   (fnil conj [])
                   (if (should-eval-form? form)
                     (ana.jvm/analyze+eval form (assoc env :ns (ns-name *ns*)) opts)
                     (ana.jvm/analyze form (assoc env :ns (ns-name *ns*)) opts)))
            (recur false)))))))

(defn analyze-ns-1
  "ana.jvm/analyze-ns, but only eval the `ns` form, and non-eval analyze all others"
  ([ns] (analyze-ns-1 ns (ana.jvm/empty-env)))
  ([ns env] (analyze-ns-1 ns env {}))
  ([ns env opts]
   (env/ensure (ana.jvm/global-env)
               (let [res ^URL (utils/ns-url ns)]
                 (assert res (str "Can't find " ns " in classpath"))
                 (let [filename (str res)
                       path     (.getPath res)]
                   (when-not (get-in (env/deref-env) [::analyzed-clj path])
                     (binding [*ns*   *ns*
                               *file* filename]
                       (analyze-file- env res filename opts)))
                   (get-in @env/*env* [::analyzed-clj path]))))))

;; api that the rest of spectrum is allowed to use. Wrap ana.jvm so we know we can change them all in one place
(defn analyze-ns [ns]
  (analyze-ns-1 ns))

(defn analyze [form & opts]
  (apply ana.jvm/analyze form opts))

(s/fdef analyze-resource :args (s/cat :r url? :env (s/? map?)))
(defn analyze-resource
  ([res]
   (analyze-resource res (ana.jvm/empty-env)))
  ([res env]
   (env/ensure (ana.jvm/global-env)
               (let [filename (str res)
                     path     (.getPath res)]
                 (when-not (get-in (env/deref-env) [::analyzed-clj path])
                   (binding [*ns*   *ns*
                             *file* filename]
                     (analyze-file- env res filename {})))
                 (get-in @env/*env* [::analyzed-clj path])))))

(instrument-ns)
