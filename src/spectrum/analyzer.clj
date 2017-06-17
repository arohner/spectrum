;;   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns spectrum.analyzer
  "Analyzer for clojure code, extends tools.analyzer with JVM specific passes/forms"
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.tools.analyzer.jvm.utils :as utils]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.reader :as reader]
            [clojure.tools.reader.reader-types :as readers]
            [clojure.java.io :as io])
  (:import (clojure.lang IObj RT Compiler Var)
           java.net.URL))


(defn analyze-ns-1
  "ana.jvm/analyze-ns, but only eval the first form, analyzing all others"
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
               (with-open [rdr (io/reader res)]
                 (let [pbr (readers/indexing-push-back-reader
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
                                (if first-form?
                                  (ana.jvm/analyze+eval form (assoc env :ns (ns-name *ns*)) opts)
                                  (ana.jvm/analyze form (assoc env :ns (ns-name *ns*)) opts)))
                         (recur false))))))))
           (get-in @env/*env* [::analyzed-clj path]))))))
