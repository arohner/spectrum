(ns spectrum.flow-test
  (:require [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as spec-test]
            [spectrum.conform :as c]
            [spectrum.flow :as flow]
            [spectrum.check :as check]))

(check/maybe-load-clojure-builtins)
(check/ensure-analysis 'spectrum.flow)

;; (spec-test/instrument)

(def dummy-env {:file "spectrum.flow-test.clj"
                :line 15
                :column 1})
(def dummy-analysis {:op :invoke
                     :form '(dummy data)
                     :env dummy-env
                     :fn {:op :const
                          :form nil
                          :env dummy-env}
                     :args [{:op :const
                             :form nil
                             :env {:file "spectrum.flow-test.clj"
                                   :line 15
                                   :column 1}}]})

(deftest basic
  (is (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x))))))

(deftest maybe-assoc-var-name-works
  (is (-> (flow/flow (ana.jvm/analyze '(defn foo [x] (inc x)))) :init :expr ::flow/var))
  (is (-> (flow/flow (ana.jvm/analyze '(def foo (fn [x] (inc x))))) :init ::flow/var)))

(def dummy-param {:op :binding
                  :form 'dummy
                  :env dummy-env})

(defn test-param [x]
  (merge dummy-param x))

(deftest destructure-fn-params
  (are [spec params result] (every? (fn [[param s]]
                                      (c/equivalent? (::flow/ret-spec param) s)) (map vector (flow/destructure-fn-params params (c/parse-spec spec) false) result))
    (s/cat :x integer?) [(test-param {:name 'x__#0 :variadic? false})] [(c/parse-spec 'integer?)]
    (s/cat :x integer? :y keyword?) [(test-param {:name 'x__#0 :variadic? false}) (test-param {:name 'y__#0 :variadic? false})] [(c/parse-spec 'integer?) (c/parse-spec 'keyword?)]

    (s/+ integer?) [(test-param {:name 'x__#0 :variadic? false}) (test-param {:name 'xs__#0, :variadic? false})] [(c/parse-spec 'integer?) (c/parse-spec 'integer?)]
    (s/+ integer?) [(test-param {:name 'x__#0 :variadic? false}) (test-param {:name 'xs__#0, :variadic? true})] [(c/parse-spec 'integer?) (c/parse-spec (s/cat :x (s/* integer?)))])

  (testing "truthy"
    (are [params spec macro?] (every? c/conformy? (map ::flow/ret-spec (flow/destructure-fn-params params spec macro?)))
      [(test-param {:name '&form__#0}) (test-param {:name '&env__#0}) (test-param {:name 'decl__#0 :variadic? true})] (:args (c/parse-spec (s/spec 'clojure.core/let))) true)))

(deftest conforming-java-method
  (testing "truthy"
    (are [cls method args] (c/conformy? (flow/get-conforming-java-method cls method args))
      clojure.lang.Namespace 'find (c/cat- [(c/value 'clojure.core)])
      clojure.lang.Namespace 'find (c/cat- [(c/unknown {:message ""})])
      clojure.lang.Numbers 'add (c/cat- [(c/unknown {:message ""}) (c/unknown {:message ""})])
      clojure.lang.Var 'hasRoot (c/cat- [])))
  (testing "falsey"
    (are [cls method args] (nil? (flow/get-conforming-java-method cls method args))
      clojure.lang.Namespace 'find (c/cat- [(c/value 3)])
      clojure.lang.Namespace 'bogus (c/cat- [(c/value 'clojure.core)]))))

(deftest conforming-java-method-arity
  (is (= 2 (-> (flow/get-conforming-java-method clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object)]))
               :parameter-types
               (count))))

  (is (= 3 (-> (flow/get-conforming-java-method clojure.lang.RT 'get (c/cat- [(c/class-spec Object) (c/class-spec Object) (c/class-spec Object)]))
               :parameter-types
               (count)))))

(deftest java-method-spec
  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/cat- [(c/value 3)]))
          :ret
          (= (c/class-spec Long/TYPE))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i double?)))
          :ret
          (= (c/class-spec Double/TYPE))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/cat- [(c/class-spec Byte/TYPE)]))
          :ret
          (= (c/class-spec Long/TYPE))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/cat- [(c/class-spec Float/TYPE)]))
          :ret
          (= (c/class-spec Double/TYPE))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/cat- [(c/class-spec clojure.lang.BigInt)]))
          :ret
          (= (c/or- [(c/class-spec Number) (c/value nil)]))))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'inc (c/parse-spec (s/cat :i int?)))
          :ret))

  (is (-> (flow/get-java-method-spec clojure.lang.Symbol 'equals (c/cat- [(c/value 'clojure.core)]))
          :ret
          c/known?))

  (is (-> (flow/get-java-method-spec java.util.Map 'entrySet (c/cat- []))
          :ret
          c/known?))

  (is (-> (flow/get-java-method-spec clojure.lang.LockingTransaction 'runInTransaction (c/cat- [(c/parse-spec (s/and fn? ifn?))]))
          :ret
          c/known?))
  (is (-> (flow/get-java-method-spec clojure.lang.Var 'hasRoot (c/cat- []))
          :ret
          c/known?))

  (is (-> (flow/get-java-method-spec clojure.lang.Indexed 'nth (c/cat- [(c/value 0)]))
          :ret
          c/known?))

  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'add (c/cat- [(c/class-spec Long) (c/class-spec Long)]))
          :ret
          (= (c/class-spec Long/TYPE))))
  (is (-> (flow/get-java-method-spec clojure.lang.Numbers 'add (c/cat- [(c/class-spec Long/TYPE) (c/class-spec Long/TYPE)]))
          :ret
          (= (c/class-spec Long/TYPE)))))

(deftest expression-return-specs
  (are [form ret-spec] (c/valid? ret-spec (::flow/ret-spec (flow/flow (ana.jvm/analyze form))))
    '(+ 1 2) (c/parse-spec #'number?)
    '(if (even? (inc 0)) 1 "string") (c/or- [(c/value 1) (c/value "string")])
    '(let [x 1] x) (c/value 1)
    '(let [x (+ 1 2)] x) (c/parse-spec #'number?)

    '(if (map? {:foo 3}) :then :else) (c/value :then)
    '(if (not (map? {:foo 3})) :then :else) (c/value :else)))

(s/def ::integer int?)

(defn dummy-binding [name & {:as opts}]
  (merge
   {:name name
    :op :binding
    :form name
    :env dummy-env}
   opts))

(deftest arity-conform?
  (testing "should pass"
    (are [spec args] (= true (flow/arity-conform? (c/parse-spec spec) args))
      (s/cat :a int?) [(dummy-binding 'a)]
      (s/cat :a int? :b int?) [(dummy-binding 'a) (dummy-binding 'b)]

      (s/cat :a (s/+ int?)) [(dummy-binding 'a) (dummy-binding 'as :variadic? true)]

      (s/cat :a (s/keys :req [::integer])) [(dummy-binding 'a)]

      (s/tuple int?) [(dummy-binding 'a)]))

  (testing "should fail"
    (are [spec args] (= false (flow/arity-conform? (c/parse-spec spec) args))
      (s/cat :a int?) [(dummy-binding 'a) (dummy-binding 'b)]
      (s/cat :a int? :b int?) [(dummy-binding 'a)]
      (s/tuple int? int?) [(dummy-binding 'a)]
      #'int? [(dummy-binding 'a)])))

(deftest strip-control-flow
  (are [in out] (= out (flow/strip-control-flow in))
    (c/or- [(c/pred-spec #'int?) (c/recur-form 'x)]) (c/or- [(c/pred-spec #'int?)])

    (c/or- [(c/pred-spec #'int?) (c/pred-spec #'string?)]) (c/or- [(c/pred-spec #'int?) (c/pred-spec #'string?)])
    (c/or- []) (c/or- [])
    (c/or- [(c/and- [(c/pred-spec #'integer?) (c/pred-spec #'even?)]) (c/recur-form (c/cat- [(c/pred-spec #'int?)]) )]) (c/and- [(c/pred-spec #'integer?) (c/pred-spec #'even?)])))

(deftest maybe-disj-works
  (are [spec pred expected] (= expected (flow/maybe-disj-pred spec pred))
    (c/pred-spec #'integer?) (c/pred-spec #'nil?) (c/pred-spec #'integer?)
    (c/or- ['clojure.core/seq? (c/pred-spec #'nil?)]) (c/pred-spec #'seq?) (c/pred-spec #'nil?)
    (c/or- ['clojure.core/seq? (c/pred-spec #'nil?)]) (c/pred-spec #'integer?) (c/or- [(c/pred-spec #'seq?) (c/pred-spec #'nil?)])))

(deftest invoke-pred?
  (is (flow/invoke-predicate? (ana.jvm/analyze '(string? "foo"))))
  (is (not (flow/invoke-predicate? (ana.jvm/analyze '(str 3))))))

(deftest invoke-nil?
  (is (flow/invoke-nil? (ana.jvm/analyze '(nil? 3))))
  (is (not (flow/invoke-nil? (ana.jvm/analyze '(= nil 3))))))

(deftest binding-update
  (is (= [] (check/check-form '(some-> x (format x)) {:x (c/parse-spec (s/nilable string?))})))

  (is (= [] (check/check-form '(when x (format x)) {:x (c/parse-spec (s/nilable string?))})))

  (let [a (check/analyze-form '(if-let [x foo] x) {:foo (c/or- [(c/pred-spec #'string?) (c/pred-spec #'nil?)])})
        binding-name (-> a :bindings first :name)]
    (is (c/equivalent? (c/or- [(c/pred-spec #'string?) (c/pred-spec #'nil?)]) (-> (flow/find-binding a [:body :test]  binding-name) ::flow/ret-spec)))
    (is (c/equivalent? (c/pred-spec #'string?) (-> (flow/find-binding a [:body :then] binding-name) ::flow/ret-spec)))
    (is (c/equivalent? (c/or- [(c/pred-spec #'nil?) (c/pred-spec #'false?)]) (-> (flow/find-binding a [:body :else]  binding-name) ::flow/ret-spec)))

    (= (c/or- [(c/class-spec Integer) (c/value nil)]) (check/type-of '(if (instance? Integer x) x nil) {:x (c/pred-spec #'any?)}))))

(deftest get-fn-method-invoke-works
  (testing "truthy"
    (are [f spec] (flow/get-fn-method-invoke (ana.jvm/analyze f) (c/parse-spec spec))
      '(fn [x] (inc x)) (s/cat :x int?)
      '(fn
         ([x] (inc x))
         ([x y] (+ x y))) (s/cat :x int?)
      '(fn
         ([x] (inc x))
         ([x y] (+ x y))) (s/cat :x int? :y int?))

    (testing "falsey"
    (are [f spec] (nil? (flow/get-fn-method-invoke (ana.jvm/analyze f) (c/parse-spec spec)))
      '(fn [x] (min x)) (s/cat)
      '(fn [x] (inc x)) (s/cat)
      '(fn [x] (inc x)) (s/cat :x int? :y int?)
      '(fn [x y & z] (inc x)) (s/cat :x int?)))))

(s/def ::foo string?)

(deftest basic-maps
  (is (= [] (check/check-form '(def empty-fn-spec {:args nil, :ret nil, :fn nil})))))

(defprotocol DummyProtocol
  (foo [this]))

(deftest class-is-protocol
  (are [cls expected] (= expected (flow/class-is-protocol? cls))
    Integer false
    spectrum.conform.Spect true
    spectrum.flow_test.DummyProtocol true))

(deftest method-is-protocol-fn?
  (are [cls method expected] (= expected (flow/class-is-protocol? cls))
    Integer '.intValue false
    spectrum.conform.Spect 'conform* true))

(deftest infer-invoke
  (are [spec args expected] (c/equivalent? expected (flow/infer-invoke-constraints spec args))

    (:args (c/get-var-spec #'inc)) [(c/pred-spec #'any?)] (c/pred-spec #'number?)
    (:args (c/get-var-spec #'keyword)) [(c/pred-spec #'any?)] (c/or- [(c/pred-spec #'string?) (c/pred-spec #'nil?) (c/pred-spec #'any?)])

    (:args (c/get-var-spec #'map)) [(c/pred-spec #'any?) (c/pred-spec #'any?)] (c/parse-spec (s/cat :x (s/or :f ifn? :k keyword?) :coll (s/* ::seq-like)))
    (:args (c/get-var-spec #'map)) [(c/pred-spec #'any?) (c/pred-spec #'any?)] []))

(deftest infer-form
  (testing "truthy"
    (are [form expected] (c/equivalent? expected (check/infer-form form))
      '(fn [x] (if x true false)) (c/fn-spec (c/cat- [(c/class-spec Object)]) (c/or- [(c/value true) (c/value false)]) nil)
      '(fn [x] (keyword x)) (c/fn-spec (c/cat- [(c/pred-spec #'any?)]) (c/or- [(c/pred-spec #'keyword?) (c/pred-spec #'nil?)]) nil)
      '(fn [x] (keyword "foo" x)) (c/fn-spec (c/cat- [(c/pred-spec #'string?)]) (c/or- [(c/pred-spec #'keyword?) (c/pred-spec #'nil?)]) nil)
      '(fn [x] (inc x)) (c/fn-spec (c/cat- [(c/or- [(c/class-spec Object) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)])]) (c/or- [(c/class-spec Number) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)]) nil)
      '(fn [x] (inc x) (keyword x) x) (c/fn-spec (c/cat- [(c/or- [(c/class-spec Object) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)])]) (c/or- [(c/class-spec Number) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)]) nil)
      '(fn [x] (not (even? x))) (c/fn-spec (c/cat- [(c/pred-spec #'integer?)]) (c/pred-spec #'boolean?) nil)

      '(fn [x] (+)) (c/fn-spec (c/cat- [(c/or- [(c/class-spec Object) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)])]) (c/or- [(c/class-spec Number) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)]) nil)
      '(fn [x] (+ x 1)) (c/fn-spec (c/cat- [(c/or- [(c/class-spec Object) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)])]) (c/or- [(c/class-spec Number) (c/class-spec Long/TYPE) (c/class-spec Double/TYPE)]) nil)
      '(fn [x] (-> x :foo)) (c/fn-spec (c/cat- [(c/pred-spec #'any?)]) (c/pred-spec #'any?) nil)))
  (testing "invalid"
    (are [form] (c/invalid? (check/infer-form form))
      '(fn [x] (inc (str x)))
      '(fn [x] (inc x) (x :foo)))))
