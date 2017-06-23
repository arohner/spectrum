(ns spectrum.classpath
  (:require [clojure.java.io :as io]
            [clojure.string :as string]
            [cognitect.transit :as t])
  (:import [java.net URL URLClassLoader]
           [java.io ByteArrayOutputStream PipedInputStream PipedOutputStream]))

;; from weavejester/clj-daemon, which doesn't have official releases

(defn url-classloader [urls]
  (println "url-classloader" urls)
  (URLClassLoader.
   (into-array URL (map io/as-url urls))
   (.getParent (.getClassLoader clojure.lang.RT))))

(defmacro with-classloader [cl & body]
  `(binding [*use-context-classloader* true]
     (let [cl# (.getContextClassLoader (Thread/currentThread))]
       (try (.setContextClassLoader (Thread/currentThread) ~cl)
            ~@body
            (finally
             (.setContextClassLoader (Thread/currentThread) cl#))))))

(defn- invoke-in [cl class-method signature & params]
  (let [class     (.loadClass cl (namespace class-method))
        signature (into-array Class (or signature []))
        method    (.getDeclaredMethod class (name class-method) signature)]
    (.invoke method class (into-array Object params))))

(defn eval-string
  "Eval the given string in a separate classloader."
  [cl string]
  (println "isolated eval:" string)
  (with-classloader cl
    (let [form   (invoke-in cl 'clojure.lang.RT/readString [String] string)
          result (invoke-in cl 'clojure.lang.Compiler/eval [Object] form)]
      (invoke-in cl 'clojure.lang.RT/printString [Object] result))))

(defn eval-transit
  "Eval the string, return transit. Use for large return values (i.e. analysis results)"
  [cl string]
  (with-classloader cl
    (let [form   (invoke-in cl 'clojure.lang.RT/readString [String] string)
          result (invoke-in cl 'clojure.lang.Compiler/eval [Object] form)
          baos (java.io.ByteArrayOutputStream.)]
      (with-open [pipe-in (PipedInputStream.)]
        (let [pipe-out (PipedOutputStream. pipe-in)
              writer (t/writer pipe-out :json)
              reader (t/reader pipe-in :json)
              f (future (t/write writer result))]
          (t/read reader))))))

(defn new-isolated-classloader []
  (-> (System/getProperty "java.class.path")
      (string/split #":")
      (->>
       (map io/file)
       (url-classloader))))

(def isolated-classloader (delay (new-isolated-classloader)))

(defn eval-with-isolated-classloader [str]
  (eval-string @isolated-classloader str))
