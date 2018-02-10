(defproject spectrum "0.1.5-SNAPSHOT"
  :description "Static 'type' checking for clojure.spec"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.9.0"]
                 [org.clojure/tools.analyzer.jvm "0.7.0"]
                 [org.clojure/test.check "0.9.0"]
                 [org.clojure/core.memoize "0.5.8"]
                 [com.cognitect/transit-clj "0.8.300"]
                 [org.clojure/core.match "0.3.0-alpha4"]]

  :profiles
  {:dev {:dependencies [[org.clojure/tools.namespace "0.2.11"]
                        [arohner/repl-utils "0.1.0"]]
         :repl-options {:init-ns spectrum.repl
                        :init (do
                                (print "hello")
                                (set! *print-level* 5)
                                (set! *print-length* 20))}}}
  :deploy-repositories [["releases" {:url "https://clojars.org/repo"
                                     :creds :gpg}]]
  :jvm-opts ["-Xmx1024m"
             "-XX:-OmitStackTraceInFastThrow"
             "-XX:+UseConcMarkSweepGC"
             "-Dfile.encoding=UTF-8"
             ;; "-agentlib:jdwp=transport=dt_socket,address=8000,server=y,suspend=n"
             ])
