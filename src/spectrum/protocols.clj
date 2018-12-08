(ns spectrum.protocols)

(defprotocol Spect
  (conform* [spec x]
    "Return the conforming value or invalid")
  (explain* [spec path via in x]))

(defprotocol DependentSpecs
  (dependent-specs- [spec]
    "Extra specs that are true of every instance of this type."))

(defprotocol KeysGet
  (keys-get- [this key]))

(defprotocol WillAccept
  (will-accept- [spec]
    "Return the spect that will make (derivative spec x) return truthy (not reject/invalid). Return nil when the spect is a regex, but complete. Return reject/invalid when it isn't legal to call derivative on spect"))

(defprotocol SpecToClasses
  (spec->classes- [this]))

(defprotocol Regex
  (derivative
    [spec x]
    "Given a parsed spec, return the derivative")
  (disentangle [this]
    "Given a spec containing choices, such as `or` or `alt`, return a
seq of concrete specs that don't contain choices")
  (re-explain* [spec path via in x])
  (empty-regex [this]
    "The empty pattern for this regex")
  (accept-nil? [this]
    "True if this pattern successfully matches")
  (return- [this]
    "Given a completed regex parse, return the conform matching value")
  (re-conj-return [this s splice?]
    "Add s to this regex. Non-regexes should return s")
  (regex? [this]
    "True if this spec is actually a regex, and not just a normal spec implementing the protocol")
  (constructor [this]
    "Returns a constructor function that takes :ps")
  (elements [this]
    "Returns the components of this regex. (constructor (elements this)) should round-trip")
  (min-length [this]
    "The minimum length sequence this regex will consume")
  (max-length [this]
    "The maximum length sequence this regex will consume. Returns int?. Use Integer/MAX_VALUE for unlimited")
  (fix-length [this n]
    "recursively resolve to all concrete specs of *up to* length n,
  i.e. (fix-length (seq- int?) 2) -> [(cat) (cat int?) (cat int?
  int?)]."))

(defrecord Accept [ret])

(defrecord Reject [])

(defrecord Invalid [a-loc form message])

(defrecord Unknown [form file line column])

(defrecord RecurForm [args])

(defrecord Bottom [])

(defrecord ThrowForm [s])

(defrecord Value [v type])

(defrecord Logic [name])

(defprotocol FirstRest
  (first- [this])
  (rest- [this]
    "Return a spect or nil.

    Returns nil if it's legal to call `rest` on this, but there are no
    items. Return `invalid` if it's not legal to call rest,
    i.e. (value :foo)"))

(defprotocol Truthyness
  (truthyness [this]
    "The truthyness of this spec, if it appeared in an `if`. Returns :truthy, :falsey or :ambiguous"))

(defprotocol Invoke
  (invoke- [s args]
    "if code calls (s args), return the expected return type")
  (invoke-accept- [s]
    "Return the most general spec this spec can be invoked with. Should probably return a regex.

 invariant: (invoke s (invoke-accept s)) => truthy"))

(defprotocol KeywordInvoke
  (keyword-invoke- [s args]
    "If code calls (:foo spec), return the expected type"))

(defrecord RegexCat [ps ks forms ret])

(defrecord RegexSeq [ps ks forms splice ret])

(defrecord RegexAlt [ps ks forms ret])

  ;; 'container' spec, for when the user does e.g. (s/cat :x (s/spec
  ;; (s/* integer?)))  necessary because it changes the behavior of
  ;; `first`. Also useful as a `delay` for forward-declared specs

(defrecord SpecSpec [s])

(defrecord PredSpec [pred form])

(defrecord ClassSpec [cls])

;;type representing a value satisfying protocol p
(defrecord ProtocolSpec [p])

(defrecord NotSpec [s])

(defrecord AndSpec [ps])

(defrecord OrSpec [ps ks])

(defrecord TupleSpec [ps])

(defrecord KeysSpec [req req-un opt opt-un])

(defrecord CollOfSpec [s kind])

(defrecord ArrayOf [s])

(defrecord MapOf [ks vs])

(defrecord FnSpec [args ret fn var methods])

(defrecord MultiSpec [multimethod retag])
