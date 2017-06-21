(ns spectrum.conform-test
  (:require [clojure.spec :as s]
            [clojure.spec.test]
            [clojure.test :refer :all]
            [clojure.tools.analyzer.jvm :as ana.jvm]
            [spectrum.conform :as c]
            [spectrum.check :as check]
            [spectrum.flow :as flow])
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
         (s/and integer? #(> % 10))
         (s/nilable int?)
         (s/coll-of ::integer)
         '[integer? integer?]))

  (testing "spect-like"
    (are [s] (s/conform ::c/spect-like (c/parse-spec s))
      (s/and #(> % 10))))

  (testing "nil"
    (is (= (c/value nil) (c/parse-spec ::s/nil))))

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

    (is (= (c/value 3) (-> {::integer 3} c/parse-spec :req ::integer c/parse-spec)))
    (is (-> (c/parse-spec (s/keys :req-un [::even-int])) :req-un :even-int)))
  (testing "fn-spec"
    (let [fs (c/parse-spec (s/fspec :args (s/cat :x string?) :ret boolean?))]
      (is (= [(c/pred-spec #'string?)]) (:args fs))
      (is (= (c/pred-spec #'boolean?)) (:ret fs)))

    (let [fs (c/parse-spec (s/fspec :args (s/cat :x string?)))]
      (is (nil? (:ret fs)))))
  (testing "seq-of"
    (is (= (c/pred-spec #'seqable?) (-> (c/parse-spec '(clojure.spec/* clojure.core/seqable?)) :ps first c/parse-spec)))))

(deftest any-spec-works
  (testing "truthy"
    (are [s] (c/any-spec? s)
      (c/pred-spec #'any?)
      (-> (c/pred-spec #'any?) (c/resolve-pred-spec) :args c/first*)))
  (testing "falsey"
    (are [s] (not (c/any-spec? s))
      (c/pred-spec #'integer?))))

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
      (c/pred-spec #'any?) (c/unknown {:message ""})
      (c/parse-spec #'even?) (c/pred-spec #'even?)
      (c/pred-spec #'integer?) (c/parse-spec #'even?)
      (c/pred-spec #'even?) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)])
      (c/pred-spec #'any?) (c/pred-spec #'boolean?)
      (c/pred-spec #'any?) (c/pred-spec #'integer?)
      (c/pred-spec #'int?) (c/pred-spec #'int?)
      (c/pred-spec #'number?) (c/class-spec Long)
      (c/pred-spec #'number?) (c/class-spec Long/TYPE)

      (c/class-spec Long) (c/value 3)
      (c/class-spec Long) (c/class-spec Long/TYPE)
      (c/class-spec Long/TYPE) (c/class-spec Long)
      (c/class-spec Long/TYPE) (c/class-spec Long/TYPE)
      (c/class-spec String) (c/class-spec String)
      (c/pred-spec #'class?) (c/class-spec String)
      (c/class-spec Object) (c/value nil)
      (c/class-spec String) (c/pred-spec #'any?)

      (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'keyword?)]) (c/value ["foo" :bar])
      (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'keyword?)]) (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'keyword?)])

      (c/tuple-spec []) (c/value [])
      (c/tuple-spec []) (c/tuple-spec [])
      (c/not-spec (c/pred-spec #'string?)) (c/pred-spec #'keyword?)

      (c/and-spec [(c/not-spec (c/pred-spec #'string?)) (c/not-spec (c/pred-spec #'keyword?))]) (c/class-spec Long)

      (c/and-spec [(c/class-spec Long) (c/not-spec (c/pred-spec #'keyword?))]) (c/class-spec Long)))

  (testing "should pass"
    (are [spec val expected] (= expected (c/conform (c/parse-spec spec) val))

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/class-spec Long) (c/class-spec Long)
         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/class-spec String) (c/class-spec String)

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)])

         (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec String) (c/class-spec Long)]) (c/or- [(c/class-spec String) (c/class-spec Long)])

         (c/or- [(c/class-spec Long) (c/class-spec String) (c/class-spec Keyword)]) (c/or- [(c/class-spec Long) (c/class-spec String)]) (c/or- [(c/class-spec Long) (c/class-spec String)])

         (c/pred-spec #'number?) (c/class-spec Long) (c/class-spec Long)
         (s/cat :x integer?) (c/parse-spec (s/cat :x integer?)) {:x (c/pred-spec #'integer?)}

         (s/and integer? even?) (c/value 10) (c/value 10)
         (s/and integer? even?) (c/parse-spec (s/and integer? even?)) (c/parse-spec (s/and integer? even?))
         (c/pred-spec #'int?) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)]) (c/and-spec [(c/pred-spec #'int?) (c/pred-spec #'even?)])
         (s/or :int integer? :str string?) (c/value "foo") [:str (c/value "foo")]
         (s/or :int integer? :str string?) (c/pred-spec #'string?) [:str (c/parse-spec 'string?)]

         (c/or- [(c/pred-spec #'seq?) (c/pred-spec #'nil?)]) (c/or- [(c/and-spec [(c/pred-spec #'seq?) (c/pred-spec #'any?)]) (c/pred-spec #'nil?)]) (c/or- [(c/and-spec [(c/pred-spec #'seq?) (c/pred-spec #'any?)]) (c/pred-spec #'nil?)])

         (s/* integer?) (c/value []) []
         (s/* integer?) (c/value [1]) [(c/value 1)]
         (s/* integer?) (c/cat- [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]) [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]

         (s/alt :int integer? :str string?) (c/value ["foo"]) [:str (c/value "foo")]

         (s/cat :x integer?) (c/value [5]) {:x ( c/value 5)}
         (s/cat :x integer? :y keyword?) (c/value [5 :foo]) {:x (c/value 5) :y (c/value :foo)}

         (s/+ integer?) (c/value [1]) [(c/value 1)]
         (s/+ integer?) (c/value [1 2]) [(c/value 1) (c/value 2)]

         (s/? integer?) (c/value []) (c/value nil)
         (s/? integer?) (c/value [1]) (c/value 1)

         (c/parse-spec (s/form (s/? integer?))) (c/value [1]) (c/value 1)

         (s/+ integer?) (c/cat- [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]) [(c/pred-spec #'integer?) (c/pred-spec #'integer?)]

         (s/* (s/alt :int integer? :str string?)) (c/value ["foo" 3]) [[:str (c/value "foo")] [:int (c/value 3)]]

         (c/cat- []) (c/cat- []) []

         (c/cat- [(c/class-spec Object)]) (c/cat- [(c/value nil)]) [(c/value nil)]
         (c/cat- [(c/class-spec Object)]) (c/cat- [(c/value nil)]) [(c/value nil)]
         (c/cat- [(c/class-spec Object) (c/class-spec Object)]) (c/cat- [(c/coll-of (c/pred-spec #'int?)) (c/value nil)]) [(c/coll-of (c/pred-spec #'int?)) (c/value nil)]
         (s/cat :x (s/* integer?) :y (s/+ string?)) (c/value ["foo"]) {:y [(c/value "foo")]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) (c/value [1 "foo"]) {:x [(c/value 1)] :y [(c/value "foo")]}
         (s/cat :x (s/* integer?) :y (s/+ string?)) (c/value [1 2 "foo" "bar"]) {:x [(c/value 1) (c/value 2)] :y [(c/value "foo") (c/value "bar")]}
         (s/cat :x (s/? integer?)) (c/value []) {}

         (s/cat :a integer? :b (s/? keyword?) :c integer?) (c/value [1 2]) {:a (c/value 1) :c (c/value 2)}
         (s/cat :a integer? :b (s/? keyword?) :c integer?) (c/value [1 :foo 2]) {:a (c/value 1) :b (c/value :foo) :c (c/value 2)}

         (s/cat :x integer?) (c/parse-spec (s/cat :x integer?)) {:x (c/pred-spec #'integer?)}

         (s/cat :x string?) (c/cat- [(c/class-spec String)]) {:x (c/class-spec String)}

         (c/keys-spec {::integer (c/value 3)} {} {} {}) (c/value {::integer 3}) (c/value {::integer 3})
         (s/keys :req [::integer]) (c/keys-spec {::integer (c/value 3)} {} {} {}) (c/keys-spec {::integer (c/value 3)} {} {} {})

         (s/keys :req [::integer] :opt-un [::string]) (c/keys-spec {::integer (c/value 3) ::string (c/value "foo")} {} {} {}) (c/keys-spec {::integer (c/value 3) ::string (c/value "foo")} {} {} {})

         (s/keys :req [::integer] :opt-un [::string]) (c/parse-spec (s/keys :req [::integer ::string])) (c/parse-spec (s/keys :req [::integer ::string]))

         (s/keys :req [::integer]) (c/parse-spec (s/keys :req [::integer] :opt-un [::foo])) (c/parse-spec (s/keys :req [::integer] :opt-un [::foo]))

         (s/cat :args (s/keys :req-un [::integer])) (c/cat- [(c/value {:integer 3})]) {:args (c/value {:integer 3})}

         (c/pred-spec #'map?) (c/parse-spec (s/keys :req [::integer])) (c/parse-spec (s/keys :req [::integer]))

         (c/or- [(c/pred-spec #'map?) (c/pred-spec #'associative?)]) (c/keys-spec {} {} {} {}) (c/keys-spec {} {} {} {})

         (c/class-spec java.util.concurrent.Callable) (c/pred-spec #'ifn?) (c/parse-spec #'ifn?)

         (c/class-spec java.util.concurrent.Callable) (c/parse-spec (s/and fn? ifn?)) (c/parse-spec (s/and fn? ifn?))

         (c/cat- [(c/class-spec java.util.concurrent.Callable)]) (c/cat- [(c/and-spec [(c/pred-spec #'fn?) (c/pred-spec #'ifn?)])]) [(c/and-spec [(c/pred-spec #'fn?) (c/pred-spec #'ifn?)])]

         (s/coll-of int?) (c/coll-of (c/pred-spec #'int?)) (c/coll-of (c/pred-spec #'int?))
         (c/or- [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/or- [(c/pred-spec #'int?) (c/pred-spec #'nil?)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/and-spec [(c/pred-spec #'int?) (c/value true)]) (c/pred-spec #'int?) (c/pred-spec #'int?)

         (c/cat- []) (c/value []) []

         (c/class-spec clojure.lang.IPersistentMap) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)]) (c/or- [(c/parse-spec (s/keys :req-un [::integer])) (c/pred-spec #'map?)])

         (c/coll-of (c/pred-spec #'any?)) (c/value [:foo]) (c/value [:foo])

         (c/coll-of (c/pred-spec #'int?)) (c/value []) (c/value [])

         (c/class-spec Object) (c/pred-spec #'nil?) (c/pred-spec #'nil?)
         (c/class-spec Object) (c/value nil) (c/value nil)
         (c/cat- [(c/class-spec Object) (c/class-spec Object)]) (c/cat- [(c/pred-spec #'nil?) (c/value nil)]) [(c/pred-spec #'nil?) (c/value nil)]
         (c/pred-spec #'coll?) (c/value [1 2 :foo]) (c/value [1 2 :foo])
         (c/seq-of (c/pred-spec #'any?)) (c/seq-of (c/pred-spec #'any?)) [(c/pred-spec #'any?)]))

  (testing "should fail"
    (are [spec val] (c/invalid? (c/conform (c/parse-spec spec) val))
      (c/pred-spec #'integer?) (c/value "foo")
      (c/pred-spec #'integer?) (c/parse-spec #'keyword?)
      (c/pred-spec #'integer?) (c/parse-spec (s/or :int integer? :str string?))
      (c/pred-spec #'even?) (c/unknown {:message ""})
      (c/parse-spec (s/and integer? even?)) (c/value 13)
      (c/parse-spec even?) (c/pred-spec #'integer?)
      (c/parse-spec (s/and integer? even?)) (c/pred-spec #'integer?)
      (s/* integer?) (c/value ["foo"])
      (s/+ integer?) (c/value [])
      (s/+ integer?) (c/value [1 2 "foo"])
      (s/? integer?) (c/value 3)
      (s/? integer?) (c/value ["foo"])
      (s/? integer?) (c/value [1 2])
      (s/cat :x integer?) (c/value [:foo])
      (s/cat :x integer? :y keyword?) (c/value [3])
      (s/cat :x integer? :y keyword?) (c/value 3)
      (s/alt :int integer? :str string?) (c/value ["foo" 3])
      (s/cat :x keyword?) (c/value [3])
      ;; (c/pred-spec #'int?) (c/cat- [(c/pred-spec #'int?)]) TODO

      (c/class-spec String) (c/value 3)

      (c/value 1) (c/value 2)

      (s/keys :req [::integer] :opt [::string]) (c/value {::integer 3 ::string 5}) ;; should fail because string doesn't conform
      (s/keys :req [::integer] :opt [::string]) (c/value {::string "foo"})

      (s/coll-of int?) (c/parse-spec (s/coll-of string?))
      (c/pred-spec #'string?) (c/or- [(c/class-spec Number) (c/value :foo)])
      (c/coll-of (c/pred-spec #'int?)) (c/unknown {:form '(mapv flow as) :message ""})
      (c/coll-of (c/pred-spec #'int?)) nil

      (c/parse-spec ::ana.jvm/analysis) (c/value 3)
      (c/parse-spec ::ana.jvm/analysis) (c/value {})

      (c/regex-seq (c/pred-spec #'integer?)) (c/or- [(c/pred-spec #'string?) (c/pred-spec #'nil?)])

      (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'keyword?)]) (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'string?)])

      (c/tuple-spec [(c/pred-spec #'string?) (c/pred-spec #'keyword?)]) (c/value 3)
      (c/tuple-spec []) (c/value 1)
      (c/tuple-spec []) (c/value [1])
      (c/tuple-spec [(c/pred-spec #'integer?)]) (c/tuple-spec [])

      (c/not-spec (c/pred-spec #'string?)) (c/pred-spec #'string?)

      (c/class-spec Long) (c/class-spec Short)
      (c/class-spec Short) (c/class-spec Long)
      (c/class-spec Long) (c/class-spec Double))))

(deftest first-rest
  (is (= (c/parse-spec 'integer?) (c/first* (c/parse-spec (s/+ integer?)))))
  ;;TODO don't know why this fails
  ;;(is (c/regex-seq? (c/rest* (c/parse-spec (s/* integer?)))))
  (is (c/cat-spec? (c/rest* (c/parse-spec (s/+ integer?)))))
  (is (nil? (c/rest* (c/cat- []))))

  (is (= (c/pred-spec #'string?) (c/second* (c/cat- [(c/class-spec String) (c/parse-spec #'string?)]))))

  (is (= (c/pred-spec #'int?) (c/first* (c/parse-spec (s/cat :x int?)))))
  (is (nil? (c/rest* (c/parse-spec (s/cat :x int?)))))
  (is (= (c/value false) (c/second* (c/cat- [(c/pred-spec #'false?) (c/value false)]))))

  (is (= (c/value 1) (c/first* (c/value [1 2 3]))))
  (is (= (c/value [2 3]) (c/rest* (c/value [1 2 3]))))

  (is (= (c/cat- [(c/unknown {:message ""})]) (c/rest* (c/cat- [(c/unknown {:message ""}) (c/unknown {:message ""})])))))

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
  (are [s expected] (= expected (c/dependent-specs s))
    (c/pred-spec #'even?) #{(c/pred-spec #'integer?)}))

(s/def ::a string?)
(s/def ::nilable-string string?)
(s/def ::b int?)
(s/def ::r double?)
(s/def ::recursive-map (s/keys :req [::r] :req-un [::a ::b] :opt-un [::recursive-map]))

(deftest recursive-map-works
  (is (c/parse-spec ::recursive-map))
  (is (c/conform (c/parse-spec ::recursive-map) (c/value {::r 3.0 ::a "foo" ::b 1})))
  (is (c/conform (c/parse-spec ::recursive-map) (c/parse-spec ::recursive-map))))

(s/def ::recursive-cat (s/cat :a ::a :b (s/? ::recursive-cat)))

(deftest recursive-cat-works
  (is (c/parse-spec ::recursive-cat))
  (is (c/conform (c/parse-spec ::recursive-cat) (c/value ["a"])))
  (is (c/conform (c/parse-spec ::recursive-cat) (c/value ["a" "a" "a"])))
  (is (c/conform (c/parse-spec ::recursive-cat) (c/parse-spec ::recursive-cat))))

(deftest re-conform-works
  (is (c/invalid? (c/re-conform (c/regex-seq (c/pred-spec #'integer?)) (c/pred-spec #'string?)))))

(deftest merge-works
  (is (= (c/parse-spec (s/keys :req [::a ::b])) (c/parse-spec (s/merge (s/keys :req [::a]) (s/keys :req [::b]))))))

(deftest keyword-invoke-works

  (are [result spec args] (c/valid? (c/keyword-invoke spec args) result )
    (c/value nil) (c/value 3) (c/cat- [(c/value ::a)])
    (c/value ::b) (c/value 3) (c/cat- [(c/value ::a) (c/value ::b)])

    (c/value 5) (c/value {:foo 5}) (c/cat- [(c/value :foo)])
    (c/pred-spec #'string?) (c/parse-spec (s/keys :req [::a])) (c/cat- [(c/value ::a)])
    (c/pred-spec #'string?) (c/parse-spec (s/keys :req [::a])) (c/cat- [(c/value ::a) (c/value ::b)])

    (c/or- [(c/pred-spec #'string?) (c/value nil)]) (c/parse-spec (s/keys :opt [::a])) (c/cat- [(c/value ::a)])
    (c/or- [(c/pred-spec #'string?) (c/value nil)]) (c/parse-spec (s/nilable (s/keys :opt [::a]))) (c/cat- [(c/value ::a)])

    (c/or- [(c/pred-spec #'string?) (c/value ::b)]) (c/parse-spec (s/keys :opt [::a])) (c/cat- [(c/value ::a) (c/value ::b)]))

  (testing "invalid"
    (are [spec args] (c/invalid? (c/keyword-invoke spec args))
      (c/value 3) (c/cat- [(c/value ::a) (c/value ::b) (c/value ::c)]))))

(deftest equivalent?
  (testing "truthy"
    (are [s1 s2] (c/equivalent? s1 s2)
      (c/pred-spec #'nil?) (c/value nil)))
  (testing "falsey"
    (are [s1 s2] (not (c/equivalent? s1 s2))
      (c/pred-spec #'integer?) (c/value 3)
      (c/value 3) (c/pred-spec #'integer?))))

(deftest or-disj
  (is (= (c/pred-spec #'int?) (c/or-disj (c/or- [(c/pred-spec #'int?) (c/value nil)]) (c/value nil))))

  (is (= (c/or- [(c/pred-spec #'int?) (c/pred-spec #'string?)]) (c/or-disj (c/or- [(c/pred-spec #'int?) (c/value nil) (c/or- [(c/pred-spec #'string?) (c/value nil)])]) (c/value nil))))

  (is (= (c/or- [(c/pred-spec #'int?) (c/pred-spec #'string?)]) (c/or-disj (c/or- [(c/pred-spec #'int?) (c/value nil) (c/or- [(c/pred-spec #'string?) (c/value nil)])]) (c/pred-spec #'nil?))))

  (is (= (c/or- [(c/pred-spec #'int?) (c/pred-spec #'string?)]) (c/or-disj (c/or- [(c/pred-spec #'int?) (c/pred-spec #'nil?) (c/or- [(c/pred-spec #'string?) (c/value nil)])]) (c/value nil))))

  (is (c/spect? (c/or-disj (c/or- [(c/value nil) (c/value nil)]) (c/value nil)))))

(deftest var-predicate
  (testing "truthy"
    (are [v] (c/var-predicate? v)
      #'int?
      #'string?
      #'false?
      #'nil?
      #'boolean?))
  (testing "falsey"
    (are [v] (not (c/var-predicate? v))
      #'not
      #'boolean
      #'print
      #'int
      #'str)))

(deftest multispecs
  (is (c/equivalent? (c/parse-spec (s/nilable (s/spec ::ana.jvm/analysis))) (check/type-of '(-> a :fn) {:a (c/parse-spec ::ana.jvm/analysis)})))
  (is (c/valid? (c/parse-spec ::ana.jvm/analysis) (-> (c/parse-spec ::ana.jvm/analysis) :ps second))))

(deftest will-accept-works
  (are [s expected] (= expected (c/will-accept s))
    (c/cat- [(c/pred-spec #'integer?)]) #{(c/pred-spec #'integer?)}
    (c/parse-spec (s/cat :x (s/? keyword?) :y integer?)) #{(c/pred-spec #'keyword?) (c/pred-spec #'integer?)}
    (c/parse-spec (s/? keyword?)) #{(c/pred-spec #'keyword?) (c/accept (c/value nil))}
    (c/derivative (c/parse-spec (s/+ keyword?)) (c/pred-spec #'keyword?)) #{(c/pred-spec #'keyword?) (c/accept (c/value nil))}))

(deftest infinite-works
  (are [in expected] (= expected (c/infinite? (c/parse-spec in)))
    (s/* integer?) true
    (s/+ integer?) false
    (c/rest* (c/parse-spec (s/+ integer?))) true
    (s/cat :x integer?) false
    (s/cat :x integer? :y (s/* string?)) false
    (s/coll-of (s/or :x integer? :y (s/* string?))) true
    (c/rest* (c/parse-spec (s/cat :x integer? :y (s/* string?)))) true
    (c/rest* (c/rest* (c/parse-spec (s/cat :x integer? :y (s/+ string?))))) true))

(deftest all-possible-values
  (is (= [{:x (c/pred-spec #'integer?)}] (c/all-possible-values (c/parse-spec (s/cat :x integer?)))))
  (is (= [{:x (c/pred-spec #'integer?) :y (c/pred-spec #'integer?)}] (c/all-possible-values (c/parse-spec (s/cat :x integer? :y integer?)))))
  (is (= 2 (count (c/all-possible-values (c/parse-spec (s/cat :x (s/? integer?) :y integer?))))))

  (let [vs (set (take 5 (c/all-possible-values (c/parse-spec (s/cat :a (s/* keyword?) :b (s/* string?) :c integer?)))))]
    (are [v] (contains? vs v)
      {:c (c/pred-spec #'integer?)}
      {:a [(c/pred-spec #'keyword?)]
       :c (c/pred-spec #'integer?)}
      {:b [(c/pred-spec #'string?)]
       :c (c/pred-spec #'integer?)}
      {:a [(c/pred-spec #'keyword?)]
       :b [(c/pred-spec #'string?)]
       :c (c/pred-spec #'integer?)})))

(deftest invoke
  (testing "truthy"
    (are [spec args expected] (= expected (c/invoke (c/parse-spec spec) args))
      (c/pred-spec #'int?) (c/cat- [(c/value 3)]) (c/value true)
      (s/map-of integer? string?) (c/cat- []) (c/invalid {:message "not enough args to invoke"})
      (s/map-of integer? string?) (c/cat- [(c/pred-spec #'integer?)]) (c/or- [(c/pred-spec #'string?) (c/value nil)])

      (s/map-of integer? string?) (c/cat- [(c/pred-spec #'integer?) (c/pred-spec #'keyword?)]) (c/or- [(c/pred-spec #'string?) (c/pred-spec #'keyword?)])

      (s/map-of integer? string?) (c/cat- [(c/or- [(c/pred-spec #'integer?) (c/value nil)])]) (c/or- [(c/pred-spec #'string?) (c/value nil)])
      (s/map-of integer? string?) (c/cat- [(c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)])]) (c/or- [(c/pred-spec #'string?) (c/value nil)])

      (s/map-of integer? string?) (c/cat- [(c/and-spec [(c/pred-spec #'integer?) (c/pred-spec #'even?)])]) (c/or- [(c/pred-spec #'string?) (c/value nil)])

      (c/value #'string?) (c/cat- [(c/value "foo")]) (c/value true)
      (c/pred-spec #'float?) (c/cat- [(c/value 3)]) (c/value false)

      (c/fn-spec (c/cat- [::integer]) ::integer nil) (c/cat- [(c/pred-spec #'integer?)]) (c/pred-spec #'integer?)))

  (testing "falsey"
    (are [spec args] (c/invalid? (c/invoke spec args))
      (c/value 1) (c/cat- [(c/value 2)])
      ;; (c/pred-spec #'int?) (c/cat- [(c/cat- [(c/value 3)])])
      )))

(deftest fnspec
  (testing "truthy"
    (are [spec args] (c/valid? spec args)
      (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) (c/pred-spec #'int?) nil) (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) (c/pred-spec #'int?) nil)
      (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) nil  nil) (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) (c/cat- [(c/pred-spec #'int?)]) nil)
      (c/fn-spec nil nil nil) (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) (c/pred-spec #'int?) nil)))

  (testing "falsey"
    (are [spec args] (not (c/valid? spec args))
      (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) (c/cat- [(c/pred-spec #'int?)]) nil) (c/fn-spec (c/cat- [(c/pred-spec #'integer?)]) (c/cat- [(c/pred-spec #'integer?)]) nil)
      (c/fn-spec nil (c/pred-spec #'int?) nil) (c/fn-spec (c/cat- [(c/pred-spec #'int?)]) nil nil))))

(deftest more-specific-spec
  (are [a b] (= true (c/more-specific-spec? a b))
    (c/class-spec Long) (c/class-spec Number)
    (c/or- [(c/class-spec Long) (c/class-spec Integer)]) (c/class-spec Number)))

(deftest keys-get
  (are [spec key expected] (= expected (c/keys-get spec key))
    (c/keys-spec {} {:integer (c/value 1)} {} {}) :integer (c/value 1)
    (c/and-spec [(c/keys-spec {} {:integer (c/value 1)} {} {}) (c/not-spec (c/pred-spec #'seq?))]) :integer (c/value 1)
    (c/keys-spec {} {:integer (c/value 1)} {} {}) :bogus nil))
