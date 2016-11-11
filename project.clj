(defproject spectrum "0.1.1-SNAPSHOT"
  :description "Static 'type' checking for clojure.spec"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.9.0-alpha14"]
                 [org.clojure/tools.analyzer.jvm "0.6.10"]
                 [org.clojure/test.check "0.9.0"]]
  :profiles
  {:dev {:dependencies [[org.clojure/tools.namespace "0.2.11"]
                        [arohner/repl-utils "0.1.0"]]
         :repl-options {:init-ns spectrum.repl}}}
  :deploy-repositories [["releases" {:url "https://clojars.org/repo"
                                     :creds :gpg}]]
  :jvm-opts ["-Xmx1024m"
             "-XX:-OmitStackTraceInFastThrow"
             "-XX:+UseConcMarkSweepGC"
             "-Dfile.encoding=UTF-8"])
