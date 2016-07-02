(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]))

(s/fdef foo :args integer? :ret integer?)

(deftest basic
  (is (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x))))))

(deftest maybe-assoc-var-name-works
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr ::flow/var))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init ::flow/var)))

(deftest maybe-assoc-fn-specs
  (is (-> (flow/flow (ana.jvm/analyze+eval '(do (in-ns 'spectrum.flow-test) (defn foo [x] (inc x))))) :ret :init :expr ::flow/spec)))

(deftest destructure-fn-params
  (are [spec params result] (= result (flow/destructure-fn-params params (c/parse-spec spec)))
       (s/cat :x integer?) '[{:name x__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/spec (c/parse-spec 'integer?)}]
       (s/cat :x integer? :y keyword?) '[{:name x__#0 :variadic? false} {:name y__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/spec (c/parse-spec 'integer?)}
                                                                                                         {:name 'y__#0 :variadic? false ::flow/spec (c/parse-spec 'keyword?)}]

       (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? false ::flow/spec (c/parse-spec 'integer?)}]
       (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? true}] [{:name 'x__#0 :variadic? false ::flow/spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? true ::flow/spec (c/parse-spec (s/* integer?))}]))

(deftest form-spec
  (are [form path spec] (= spec (get-in (ana.jvm/analyze+eval `(do (in-ns 'spectrum.flow-test ~form))) path))
       '(defn foo [x] (inc x)) [:ret :init :expr :methods first :body] (c/parse-spec 'integer?)))

(deftest java-method-spec
  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i long?)))
          :ret
          (= (c/parse-spec 'long?))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i double?)))
          :ret
          (= (c/parse-spec 'double?))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i integer?)))
          :ret))
  )
