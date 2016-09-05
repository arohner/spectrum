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
(s/def ::foo string?)

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
         (s/coll-of ::integer)
         '[integer? integer?]))

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
    (is (= (c/value 3) (c/parse-spec 3)))
    (is (c/value? (c/parse-spec '[integer? integer?]))))

  (testing "keys"
    (are [spec] (c/spect? (c/parse-spec spec))
      (s/keys :req [::even-int])
      (s/keys :req-un [::even-int])
      (s/cat :args (s/keys :req-un [::integer]))
      (s/merge (s/keys :req-un [::integer]) (s/keys :req-un [::even-int]))
      {::integer 3})

    (is (= (c/value 3) (-> {::integer 3} c/parse-spec :req ::integer)))
    (is (-> (c/parse-spec (s/keys :req-un [::even-int])) :req-un :even-int)))
  (testing "fn-spec"
    (let [fs (c/parse-spec (s/fspec :args (s/cat :x string?) :ret boolean?))]
      (is (= [(c/pred-spec #'string?)]) (:args fs))
      (is (= (c/pred-spec #'boolean?)) (:ret fs)))

    (let [fs (c/parse-spec (s/fspec :args (s/cat :x string?)))]
      (is (nil? (:ret fs)))))
  (testing "seq-of"
    (is (= (c/pred-spec #'seqable?) (first (:ps (c/parse-spec '(clojure.spec/* clojure.core/seqable?))))))))

(deftest conform-works
  (testing "should return val"
    (are [spec val] (= val (c/conform spec val))
      (c/pred-spec #'integer?) (c/value 3)
      (c/pred-spec #'integer?) (c/value 3)
      (c/pred-spec #'symbol?) (c/value 'foo)
      (c/value 1) (c/value 1)
      (c/pred-spec #'integer?) (c/pred-spec #'integer?)
      (c/pred-spec #'integer?) (c/pred-spec #'integer?)
      (c/pred-spec #'integer?) (c/parse-spec (s/and integer? even?))
      (c/pred-spec #'any?) (c/pred-spec #'nil?)
      (c/parse-spec #'even?) (c/pred-spec #'even?)
      (c/pred-spec #'integer?) (c/parse-spec #'even?)
      (c/pred-spec #'even?) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)])
      (c/pred-spec #'any?) (c/pred-spec #'boolean?)
      (c/pred-spec #'any?) (c/pred-spec #'integer?)
      (c/pred-spec #'int?) (c/pred-spec #'int?)
      (c/pred-spec #'number?) (c/class-spec Long)
      (c/class-spec Long) (c/value 3)
      (c/class-spec Integer) (c/value 0)
      (c/pred-spec #'int?) (c/class-spec Long)
      (c/class-spec String) (c/class-spec String)

      (c/pred-spec #'number?) (c/pred-spec #'integer?)))

  (testing "should pass"
    (are [spec val expected] (= expected (c/conform spec val))


         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/class-spec Long) (c/class-spec Long)
         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/class-spec String) (c/class-spec String)

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)])

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec String) (c/class-spec Long)]) (c/or- [(c/class-spec String) (c/class-spec Long)])

         (c/or- [(c/class-spec Long) (c/class-spec String) (c/class-spec Keyword)]) (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)])

         (c/parse-spec #'number?) (c/class-spec Long) (c/class-spec Long)
         (c/parse-spec (s/cat :x integer?)) (c/parse-spec (s/cat :x integer?)) {:x (c/pred-spec #'integer?)}

         (s/and integer? even?) 10 10
         (s/and integer? even?) (c/parse-spec (s/and integer? even?)) (c/parse-spec (s/and integer? even?))
         (c/pred-spec #'int?) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)]) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)])
         (s/or :int integer? :str string?) "foo" [:str "foo"]
         (s/or :int integer? :str string?) (c/pred-spec #'string?) [:str (c/parse-spec 'string?)]

         (c/or- [(c/pred-spec #'seq?) (c/pred-spec #'nil?)]) (c/or- [(c/and-spec [(c/pred-spec #'seq?) (c/pred-spec #'any?)]) (c/pred-spec #'nil?)]) (c/or- [(c/and-spec [(c/pred-spec #'seq?) (c/pred-spec #'any?)]) (c/pred-spec #'nil?)])

         (s/* integer?) [] []
         (s/* integer?) [1] [1]
         (s/* integer?) (c/cat- [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]) [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]

         (s/alt :int integer? :str string?) ["foo"] [:str "foo"]

         (s/cat :x integer?) [5] {:x 5}
         (s/cat :x integer? :y keyword?) [5 :foo] {:x 5 :y :foo}

         (s/+ integer?) [1] [1]
         (s/+ integer?) [1 2] [1 2]

         (s/? integer?) [] nil
         (s/? integer?) [1] 1

         (c/parse-spec (s/form (s/? integer?))) [1] 1

         (s/+ integer?) (c/cat- [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]) [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]

         (s/* (s/alt :int integer? :str string?)) ["foo" 3] [[:str "foo"] [:int 3]]

         (c/cat- []) (c/cat- []) []

         (s/cat :x (s/* integer?) :y (s/+ string?)) ["foo"] {:y ["foo"]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) [1 "foo"] {:x [1] :y ["foo"]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) [1 2 "foo" "bar"] {:x [1 2] :y ["foo" "bar"]}
         (s/cat :x (s/? integer?)) [] {}

         (s/cat :a integer? :b (s/? keyword?) :c integer?) [1 2] {:a 1 :c 2}
         (s/cat :a integer? :b (s/? keyword?) :c integer?) [1 :foo 2] {:a 1 :b :foo :c 2}

         (s/cat :x integer?) (c/parse-spec (s/cat :x integer?)) {:x (c/parse-spec 'integer?)}

         (s/cat :x string?) [(c/class-spec String)] {:x (c/class-spec String)}


         (s/keys :req [::integer]) {::integer 3} {::integer 3}

         (s/keys :req [::integer] :opt-un [::string]) {::integer 3 ::string "foo"} {::integer 3 ::string "foo"}

         (s/keys :req [::integer] :opt-un [::string]) (c/parse-spec (s/keys :req [::integer ::string])) (c/parse-spec (s/keys :req [::integer ::string]))

         (s/keys :req [::integer]) (c/parse-spec (s/keys :req [::integer] :opt-un [::foo])) (c/parse-spec (s/keys :req [::integer] :opt-un [::foo]))

         (s/cat :args (s/keys :req-un [::integer])) [{:integer 3}] {:args {:integer 3}}

         (c/pred-spec #'map?) (c/parse-spec (s/keys :req [::integer])) (c/parse-spec (s/keys :req [::integer]))

         (c/or- [(c/pred-spec #'map?) (c/pred-spec #'associative?)]) (c/keys-spec {} {} {} {}) (c/keys-spec {} {} {} {})

         (c/class-spec java.util.concurrent.Callable) (c/pred-spec #'ifn?) (c/parse-spec #'ifn?)

         (c/class-spec java.util.concurrent.Callable) (c/parse-spec (s/and fn? ifn?)) (c/parse-spec (s/and fn? ifn?))

         (c/cat- [(c/class-spec java.util.concurrent.Callable)]) [(c/and-spec [(c/pred-spec #'fn?) (c/pred-spec #'ifn?)])] [(c/and-spec [(c/pred-spec #'fn?) (c/pred-spec #'ifn?)])]

         (s/coll-of int?) (c/coll-of (c/pred-spec #'int?)) (c/coll-of (c/pred-spec #'int?))
         (c/or- [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/or- [(c/pred-spec #'int?) (c/pred-spec #'nil?)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/and-spec [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/cat- []) [] []

         (c/class-spec clojure.lang.IPersistentMap) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)]) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)])

         (c/coll-of (c/pred-spec #'any?)) [:foo] [:foo]

         (c/coll-of (c/pred-spec #'int?)) [] []

         (c/class-spec Object) (c/pred-spec #'nil?) (c/pred-spec #'nil?)
         (c/class-spec Object) (c/value nil) (c/value nil)
         (c/cat- [(c/class-spec Object) (c/class-spec Object)]) [(c/pred-spec #'nil?) (c/value nil)] [(c/pred-spec #'nil?) (c/value nil)]
         (c/pred-spec #'coll?) [1 2 :foo] [1 2 :foo]

         (c/pred-spec #'seqable?) (c/class-spec clojure.lang.PersistentHashMap) (c/class-spec clojure.lang.PersistentHashMap)
         (c/pred-spec #'seqable?) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?)) (c/map-of (c/pred-spec #'any?) (c/pred-spec #'any?))))

  (testing "should fail"
    (are [spec val] (= ::c/invalid (c/conform spec val))
      (c/pred-spec #'integer?) "foo"
      ;;(s/spec #(< % 10)) 12
      (c/pred-spec #'integer?) (c/parse-spec #'keyword?)
      (c/pred-spec #'integer?) (c/parse-spec (s/or :int integer? :str string?))
      (c/pred-spec #'even?) (c/unknown nil)
      (c/parse-spec (s/and integer? even?)) (c/pred-spec #'integer?)
      (c/parse-spec (s/and integer? even?)) 13
      (c/parse-spec (s/and integer? even? #(> % 10))) (s/and integer? even?)
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

      (s/keys :req [::integer] :opt [::string]) {::integer 3 ::string 5} ;; should fail because string doesn't conform
      (s/keys :req [::integer] :opt [::string]) {::string "foo"}

      (s/coll-of int?) (c/parse-spec (s/coll-of string?))
      (c/pred-spec #'string?) (c/or- [(c/class-spec Number) (c/value :foo)])
      (c/coll-of (c/pred-spec #'int?)) (c/unknown '(mapv flow as))
      (c/coll-of (c/pred-spec #'int?)) nil)))

(deftest first-rest
  (is (= (c/parse-spec 'integer?) (c/first* (c/parse-spec (s/+ integer?)))))
  (is (c/regex-seq? (c/rest* (c/parse-spec (s/* integer?)))))
  (is (c/cat-spec? (c/rest* (c/parse-spec (s/+ integer?)))))
  (is (nil? (c/rest* (c/cat- []))))

  (is (= (c/pred-spec #'string?) (c/second* (c/cat- [(c/class-spec String) (c/parse-spec #'string?)]))))

  (is (= (c/pred-spec #'int?) (c/first* (c/parse-spec (s/cat :x int?)))))
  (is (nil? (c/rest* (c/parse-spec (s/cat :x int?)))))
  (is (= (c/value false) (c/second* (c/cat- [(c/pred-spec #'false?) (c/value false)])))))

(deftest truthyness
  (are [s expected] (= expected (c/truthyness s))
    (c/pred-spec #'boolean?) :ambiguous
    (c/pred-spec #'any?) :ambiguous
    (c/class-spec Boolean) :ambiguous

    (c/pred-spec #'integer?) :truthy
    (c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)]) :truthy

    (c/or- [(c/class-spec clojure.lang.ISeq) (c/class-spec clojure.lang.Seqable)]) :truthy

    (c/or- [(c/class-spec String) (c/class-spec Boolean)]) :ambiguous

    (c/pred-spec #'false?) :falsey
    (c/pred-spec #'true?) :truthy

    (c/value true) :truthy
    (c/value false) :falsey
    (c/class-spec Integer) :truthy
    ))

(deftest dependendent-specs
  (are [s expected] (= expected (c/dependent-specs* s))
    (c/pred-spec #'even?) #{(c/pred-spec #'integer?) (c/pred-spec #'any?)}))
