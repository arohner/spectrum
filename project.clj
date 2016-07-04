(defproject spectrum "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.9.0-alpha8"]
                 [org.clojure/tools.analyzer.jvm "0.6.10"]
                 [org.clojure/test.check "0.9.0"]]
  :profiles
  {:dev {:dependencies [[org.clojure/tools.namespace "0.2.11"]]
         :repl-options {:init-ns spectrum.repl}}})
