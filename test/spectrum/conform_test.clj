(ns spectrum.conform-test
  (:require [clojure.spec :as s]
            [clojure.spec.test]
            [clojure.test :refer :all]
            [spectrum.conform :as c])
  (:import clojure.lang.Keyword))

(clojure.spec.test/instrument)

(s/def ::integer integer?)
(s/def ::string string?)
(s/def ::even-int (s/and integer? even?))

(deftest parse-spec-works
  (testing "returns Spect"
    (are [spec] (satisfies? c/Spect (c/parse-spec spec))
         'integer?
         #'integer?
         (s/spec integer?)
         (s/spec #(< % 10))
         ::even-int
         (s/spec ::even-int)
         (s/or :int integer? :str string?)
         (s/and #(> % 10))
         (s/and integer? #(> % 10))
         (s/nilable int?)
         (s/coll-of ::integer)))

  (testing "nil"
    (= ::s/nil (c/parse-spec ::s/nil)))

  (testing "returns Regex"
    (are [spec] (c/regex? (c/parse-spec spec))
         (s/* integer?)
         (s/+ integer?)
         (s/? integer?)
         (s/alt :x integer? :y keyword?)
         (s/cat :x integer? :y keyword?)
         (s/* (s/alt :int integer? :str string?))))

  (testing "literals"
    (is (= 3 (c/parse-spec 3)))
    (is (every? #(satisfies? c/Spect %) (c/parse-spec '[integer? integer?]))))

  (testing "keys"
    (are [spec] (c/spect? (c/parse-spec spec))
      (s/keys :req [::even-int])
      (s/keys :req-un [::even-int])
      (s/cat :args (s/keys :req-un [::integer])))

    (is (-> (c/parse-spec (s/keys :req-un [::even-int])) :req-un :even-int))))

(deftest conform-works
  (testing "should pass"
    (are [spec val expected] (= expected (c/conform spec val))
         'integer? 3 3
         (s/spec #(< % 10)) 3 3
         (c/value 1) (c/value 1) (c/value 1)

         #'symbol? (c/value 'foo) (c/value 'foo)
         'integer? 'integer? (c/parse-spec 'integer?)
         #'integer? #'integer? (c/parse-spec #'integer?)
         'integer? (s/and integer? even?) (c/parse-spec 'integer?)
         'integer? (s/and integer? even?) (c/parse-spec 'integer?)

         #'number? (c/class-spec Long) (c/value true)
         #'int? (c/class-spec Long) (c/value true)
         (c/class-spec Long) 3 3
         (c/class-spec String) (c/class-spec String) (c/class-spec String)

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)])

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec String) (c/class-spec Long)]) (c/or- [(c/class-spec String) (c/class-spec Long)])

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String) (c/class-spec Keyword)]) (c/or- [(c/class-spec Long) (c/class-spec String) (c/class-spec Keyword)])

         (c/parse-spec #'number?) (c/class-spec Long) (c/value true)
         (s/cat :x integer?) (s/cat :x integer?) {:x (c/parse-spec 'integer?)}

         (s/and integer? even?) 10 10
         (s/and integer? even?) (s/and integer? even?) (c/parse-spec (s/and integer? even?))
         (s/and integer? even?) (s/and integer? even? #(> % 10)) (c/parse-spec (s/and integer? even?))
         (s/or :int integer? :str string?) "foo" [:str "foo"]
         (s/or :int integer? :str string?) 'string? [:str (c/parse-spec 'string?)]

         (s/* integer?) [] []
         (s/* integer?) [1] [1]
         (s/* integer?) '[integer? integer?] (c/parse-spec '[integer? integer?])

         (s/alt :int integer? :str string?) ["foo"] [:str "foo"]

         (s/cat :x integer?) [5] {:x 5}
         (s/cat :x integer? :y keyword?) [5 :foo] {:x 5 :y :foo}

         (s/+ integer?) [1] [1]
         (s/+ integer?) [1 2] [1 2]

         (s/? integer?) [] nil
         (s/? integer?) [1] 1

         (s/+ integer?) '[integer? integer?] (c/parse-spec '[integer? integer?])

         (s/* (s/alt :int integer? :str string?)) ["foo" 3] [[:str "foo"] [:int 3]]

         (s/cat :x (s/* integer?) :y (s/+ string?)) ["foo"] {:y ["foo"]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) [1 "foo"] {:x [1] :y ["foo"]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) [1 2 "foo" "bar"] {:x [1 2] :y ["foo" "bar"]}
         (s/cat :x (s/? integer?)) [] {}

         (s/cat :x integer?) (s/cat :x integer?) {:x (c/parse-spec 'integer?)}

         (s/cat :x string?) [(c/class-spec String)] {:x (c/class-spec String)}


         (s/keys :req [::integer]) {::integer 3} {::integer 3}

         (s/keys :req [::integer] :opt-un [::string]) {::integer 3 ::string "foo"} {::integer 3 ::string "foo"}

         (s/keys :req [::integer] :opt-un [::string]) (s/keys :req [::integer ::string]) (c/parse-spec (s/keys :req [::integer ::string]))

         (s/cat :args (s/keys :req-un [::integer])) [{:integer 3}] {:args {:integer 3}}


         #'ifn? (c/class-spec java.util.concurrent.Callable) (c/parse-spec #'ifn?)
         (s/and fn? ifn?) (c/class-spec java.util.concurrent.Callable) (c/class-spec java.util.concurrent.Callable)

         (c/class-spec java.util.concurrent.Callable) (s/and fn? ifn?) (c/parse-spec (s/and fn? ifn?))

         (s/coll-of int?) (s/coll-of int?) (c/parse-spec (s/coll-of int?))
         (c/or- [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/or- [(c/pred-spec #'int?) (c/pred-spec #'nil?)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/and-spec [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/cat- []) [] []

         (c/class-spec clojure.lang.IPersistentMap) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)]) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)])
         ))

  (testing "should fail"
    (are [spec val] (= ::c/invalid (c/conform spec val))
         'integer? "foo"
         (s/spec #(< % 10)) 12
         'integer? 'keyword?
         'integer? (s/or :int integer? :str string?)
         (s/and integer? even?) 'integer?
         (s/and integer? even?) 13
         (s/and integer? even? #(> % 10)) (s/and integer? even?)
         (s/* integer?) ["foo"]
         (s/+ integer?) []
         (s/+ integer?) [1 2 "foo"]
         (s/? integer?) 3
         (s/? integer?) ["foo"]
         (s/? integer?) [1 2]
         (s/cat :x integer?) [:foo]
         (s/cat :x integer? :y keyword?) [3]
         (s/cat :x integer? :y keyword?) 3
         (s/alt :int integer? :str string?) ["foo" 3]
         (s/cat :x keyword?) [3]
         (s/cat :x keyword?) [(c/value 3)]
         ;; (s/& (s/+ integer?) #(even? (count %))) [1]

         (c/class-spec String) 3
         (c/class-spec Integer) 3

         (c/value 1) (c/value 2)

         (s/keys :req [::integer] :opt [::string]) {::integer 3 ::string 5}
         (s/keys :req [::integer] :opt [::string]) {::string "foo"}

         (s/coll-of int?) (s/coll-of string?))))

(deftest first-rest
  (is (= (c/parse-spec 'integer?) (c/first* (c/parse-spec (s/+ integer?)))))
  (is (instance? spectrum.conform.RegexSeq (c/rest* (c/parse-spec (s/* integer?)))))
  (is (instance? spectrum.conform.RegexCat (c/rest* (c/parse-spec (s/+ integer?))))))


(deftest spect?-works)

(deftest regex?-works)

(deftest instance?-transformer
  (is (-> (c/maybe-transform #'instance? (c/parse-spec (s/get-spec #'instance?)) (c/cat- [String (c/parse-spec #'string?)])) :ret :v))

  (is (-> (c/maybe-transform #'instance? (c/parse-spec (s/get-spec #'instance?)) (c/cat- [String (c/unknown nil)])) :ret (= (c/parse-spec #'boolean?)))))

;; (s/cat :a int? :b int?)
;; (s/cat :a int? :b int? :c int?)
;; (c/rest* (c/parse-spec (s/cat :a (s/+ int?))))
