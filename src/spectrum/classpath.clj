(ns spectrum.classpath
  (:require [clojure.java.io :as io]
            [clojure.string :as string])
  (:import [java.net URL URLClassLoader]
           [java.io ByteArrayOutputStream PipedInputStream PipedOutputStream]))

(defn url-classloader [urls]
  (println "url-classloader" urls)
  (URLClassLoader.
   (into-array URL (map io/as-url urls))
   (.getParent (clojure.lang.RT/baseLoader))))

(defmacro with-classloader [cl & body]
  `(binding [*use-context-classloader* true]
     (let [cl# (.getContextClassLoader (Thread/currentThread))]
       (try (.setContextClassLoader (Thread/currentThread) ~cl)
            ~@body
            (finally
             (.setContextClassLoader (Thread/currentThread) cl#))))))

(defn- invoke-in [^ClassLoader cl class-method signature & params]
  (let [class     (.loadClass cl (namespace class-method))
        signature (into-array Class (or signature []))
        method    (.getDeclaredMethod class (name class-method) signature)]
    (.invoke method class (into-array Object params))))

(defn construct-in [^ClassLoader cl signature & params]
  (let [class     (.loadClass cl)
        signature (into-array Class (or signature []))
        constructor    (.getConstructor class signature)]
    (.newInstance constructor (into-array Object params))))

(defn clj-var-in
  "Return a var in a another runtime. Call using .invoke"
  ([^ClassLoader cl ns name]
   (invoke-in cl 'clojure.java.api.Clojure/var [Object Object] ns name))
  ([^ClassLoader cl qualified-name]
   (invoke-in cl 'clojure.java.api.Clojure/var [Object] qualified-name)))

(defn read-in [cl form]
  {:pre [(string? form)]}
  (invoke-in cl 'clojure.java.api.Clojure/read [String] form))

(defn require-in [^ClassLoader cl ns]
  {:pre [(string? ns)]}
  (.invoke (clj-var-in cl "clojure.core/require") (read-in cl ns)))

(defn eval-string
  "Eval the given string in a separate classloader."
  [cl string]
  (println "isolated eval:" string)
  (let [s (with-classloader cl
            (let [form   (invoke-in cl 'clojure.lang.RT/readString [String] string)
                  result (invoke-in cl 'clojure.lang.Compiler/eval [Object] form)]
              (invoke-in cl 'clojure.lang.RT/printString [Object] result)))]
    (read-string s)))

(defn init-cl [cl]
  (invoke-in cl 'java.lang.Class/forName [String] "clojure.java.api.Clojure")
  (invoke-in cl 'java.lang.Class/forName [String] "clojure.lang.RT")
  cl)

(defn new-isolated-classloader []
  (-> (System/getProperty "java.class.path")
      (string/split #":")
      (->>
       (map io/file)
       url-classloader
       init-cl)))

(def isolated-classloader (delay (new-isolated-classloader)))

(defn eval-with-isolated-classloader [str]
  (eval-string @isolated-classloader str))

(defn var-analysis-in [cl v]
  (-> (clj-var-in cl "spectrum.data" "get-var-analysis")
      (.invoke (clj-var-in cl (str (.ns v)) (str (.sym v))))))
