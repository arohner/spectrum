(defproject spectrum "0.2.0-SNAPSHOT"
  :description "Static 'type' checking for clojure.spec"
  :url "http://github.com/arohner/spectrum"
  :license {:name "Attribution-NonCommercial-NoDerivs 3.0 Unported"
            :url "https://creativecommons.org/licenses/by-nc-nd/3.0/"}
  :dependencies [[org.clojure/clojure "1.10.0"]
                 [org.clojure/tools.analyzer.jvm "0.7.2"]
                 [org.clojure/test.check "0.9.0"]
                 [org.clojure/core.memoize "0.5.8"]
                 [org.clojure/math.combinatorics "0.1.4"]]

  :profiles
  {:dev {:dependencies [[org.clojure/tools.namespace "0.2.11"]
                        [orchestra "2018.08.19-1"]
                        [arohner/repl-utils "0.1.0"]]
         :repl-options {:init-ns spectrum.repl
                        :init (do
                                (set! *print-level* 10)
                                (set! *print-length* 20))}}}
  :deploy-repositories [["releases" {:url "https://clojars.org/repo"
                                     :creds :gpg}]]
  :jvm-opts ["-Xmx1024m"
             "-XX:-OmitStackTraceInFastThrow"
             "-XX:+UseConcMarkSweepGC"
             "-Dfile.encoding=UTF-8"
             ;; "-agentlib:jdwp=transport=dt_socket,address=8000,server=y,suspend=n"
             ])
