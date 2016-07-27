(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec :as s]
            [clojure.spec.test :as spec-test]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]
            [spectrum.check :as check]))

(check/maybe-load-clojure-builtins)

;;(spec-test/instrument)

(deftest basic
  (is (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x))))))

(deftest maybe-assoc-var-name-works
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr ::flow/var))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init ::flow/var)))

;; (deftest destructure-fn-params
;;   (are [spec params result] (= result (flow/destructure-fn-params params (c/parse-spec spec) {}))
;;        (s/cat :x integer?) '[{:name x__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}]
;;        (s/cat :x integer? :y keyword?) '[{:name x__#0 :variadic? false} {:name y__#0 :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}
;;                                                                                                          {:name 'y__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'keyword?)}]

;;        (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? false}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)}]
;;        (s/+ integer?) '[{:name x__#0 :variadic? false} {:name xs__#0, :variadic? true}] [{:name 'x__#0 :variadic? false ::flow/ret-spec (c/parse-spec 'integer?)} {:name 'xs__#0, :variadic? true ::flow/ret-spec (c/parse-spec (s/* integer?))}]))

(deftest conforming-java-method
  (is (flow/get-conforming-java-method clojure.lang.Var 'hasRoot (c/cat- []))))

(deftest java-method-spec
  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i 3)) {})
          :ret
          (= (c/class-spec Long))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i double?)) {})
          :ret
          (= (c/class-spec Double))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i int?)) {})
          :ret))

  (is (-> (flow/get-java-method-spec clojure.lang.Symbol 'equals (c/cat- [(c/value 'clojure.core)]) {})
          :ret
          c/known?))

  (is (-> (flow/get-java-method-spec clojure.lang.LockingTransaction 'runInTransaction (c/cat- [(c/parse-spec (s/and fn? ifn?))]) {})
          :ret
          c/known?))
  (is (-> (flow/get-java-method-spec clojure.lang.Var 'hasRoot (c/cat- []) {})
          :ret
          c/known?)))

(deftest java-type->spec-works
  (are [x result] (= result (flow/java-type->spec x))
       'long (c/class-spec Long)
       String (c/class-spec String)))

(deftest expression-return-specs
  (are [form ret-spec] (c/valid? ret-spec (::flow/ret-spec (flow/flow (ana.jvm/analyze form))))
    '(+ 1 2) (c/parse-spec #'number?)
    '(if (even? *print-length*) 1 "string") (c/or- [(c/value 1) (c/value "string")])
    '(let [x 1] x) (c/value 1)
    '(let [x (+ 1 2)] x) (c/parse-spec #'number?)

    '(if (map? {:foo 3}) :then :else) (c/value :then)
    '(if (not (map? {:foo 3})) :then :else) (c/value :else)))

(s/def ::integer int?)

(deftest arity-conform?
  (testing "should pass"
    (are [spec args] (= true (flow/arity-conform? (c/parse-spec spec) args))
      (s/cat :a int?) '[a]
      (s/cat :a int? :b int?) '[a b]

      (s/cat :a (s/+ int?)) '[a {:name as :variadic? true}]

      (s/cat :a (s/keys :req [::integer])) '[a]))

  (testing "should fail"
    (are [spec args] (= false (flow/arity-conform? (c/parse-spec spec) args))
      (s/cat :a int?) '[a b]
      (s/cat :a int? :b int?) '[a]
      #'int? '[a])))
