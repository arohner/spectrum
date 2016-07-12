(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [clojure.spec.test :as spec-test]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]))

;;(spec-test/instrument)

(deftest basic
  (is (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x))))))

(deftest maybe-assoc-var-name-works
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr ::flow/var))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init ::flow/var)))

(deftest maybe-assoc-fn-specs
  (is (-> (map flow/flow (ana.jvm/analyze-ns 'spectrum.examples.good.defn)) last :init :expr ::flow/args-spec)))

(deftest destructure-fn-params
  (are [spec params result] (= result (flow/destructure-fn-params params (c/parse-spec spec)))
       (s/cat :x integer?) '[{:name x__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}]
       (s/cat :x integer? :y keyword?) '[{:name x__#0 :variadic? false} {:name y__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}
                                                                                                         {:name 'y__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'keyword?)}]

       (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}]
       (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? true}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? true ::flow/ret-spec (c/parse-spec (s/* integer?))}]))

(deftest java-method-spec
  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i 3)))
          :ret
          (= (c/class-spec Long))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i double?)))
          :ret
          (= (c/class-spec Double))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i integer?)))
          :ret)))

(deftest java-type->spec-works
  (are [x result] (= result (flow/java-type->spec x))
       'long (c/class-spec Long)
       String (c/class-spec String)))

(deftest expression-return-specs
  (are [form ret-spec] (c/valid? ret-spec (::flow/ret-spec (flow/flow (ana.jvm/analyze form))))
    '(+ 1 2) (c/parse-spec #'number?)
    '(if true 1 "string") (c/parse-spec (s/or :num number? :str string?))
    '(if true 1 2) (c/parse-spec #'number?)))
