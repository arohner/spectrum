
# spectrum

A library for doing static analysis of Clojure code, catching clojure.spec conform errors at compile time.

**Wait what?**

It's like core.typed, but it relies on clojure.spec annotations.

**So it's an optional static type system?**

Kind-of. It finds errors at compile time, and predicates kind of look like types. So sure.

![Proving contracts ahead of time](https://pbs.twimg.com/media/CphGpB5VUAAJyGL.jpg)

## Current Status

[![CircleCI](https://circleci.com/gh/arohner/spectrum.svg?style=svg)](https://circleci.com/gh/arohner/spectrum)
[![Clojars Project](https://img.shields.io/clojars/v/spectrum.svg)](https://clojars.org/spectrum)

Developer Preview. I'm now convinced it's theoretically sound, and
*most* of the core language semantics are done. The main thing it
needs now is polish and more precise specs for complicated functions,
like `map`, `filter`, `update-in`, etc.

## Goals

- usable
- pragmatic
- readable code
- fast
- configurable strictness levels
- incremental

## Non-goals

- perfection
- correctness

## Anti-goals

- requiring 100% spec coverage. Spectrum will do its best to find
  errors where it can, even if not everything is spec'd. Note that
  speccing more is recommended, but we understand other constraints
  get in the way.

In particular, spectrum aims to be fast and usable, and catching
bugs. A tool that catches 80% of bugs that you use every day is better
than a 100% tool that you don't use. Spectrum will converge on 100%,
but won't guarantee 100% correctness for a while.

## Usage

Use clojure.spec as normal. Then, at the repl or during tests:

```clojure
(require '[spectrum.check :as check])

(check/check 'your.namespace)
```

Returns a seq of Error defrecords.

### Requirements

- if you use a predicate in a spec, i.e. `(s/fdef foo :args (s/cat :x bar?))`, then `bar?` should be spec'd, or you'll get a warning

#### Defrecord / instance?

If you have a predicate that is just a simple simple `instance?` check for a class, i.e.

```clojure
(defrecord Foo ...)
(defn foo? [x] (instance? Foo x))
```
You'll want to add:
```clojure
(:require [spectrum.ann :as ann])
(ann/ann #'foo? (ann/instance-transformer Foo))
```
This tells the system that expressions tagged  w/ spec `#'foo?` are of class `Foo`, which is useful in java interop, both for Java methods that take Foo, and defrecord constructors: (`->Foo` and `map->Foo`).


## Limitations

- It's still very early. It doesn't understand all clojure forms yet, nor all spec annotations. Contributions welcome.

- It also proceeds from the assumption that your specs are correct (i.e. no spec errors at runtime). If you're not running clojure.test.spec or not running your unit tests with `instrument`, you're gonna have a bad time.


## How It Works

This section is for the curious, and potential contributors. Shouldn't be necessary to understand this to use it.

### spectrum.conform

This contains a spec parser and a re-implementation of clojure.spec, except they work on literals and specs rather than normal clojure values.

```clojure
(c/conform (s/cat :x integer?) [3])
=> {:x 3}
```

```clojure
(require '[spectrum.conform :as c])
(c/parse-spec (s/+ integer?))
```
Returns a defrecord, containing the parsed spec. This is basically a reimplementation of clojure.spec, except more data-driven. If you're not using spectrum, but want to do other analysis-y stuff with specs, you may find this useful.

```
(c/conform (s/+ integer?) [1 2 3])

(c/conform (s/+ integer?) '[integer? integer?])
```

`c/conform` behaves the same as `s/conform`, except it works on
literals and specs (i.e. the things we have access to at compile
time). For now, the best documentation is the tests,
`test/spectrum/conform_test.clj`. Spectrum conform will have 100%
coverage of clojure.spec, but isn't done yet. If you encounter a spec
that spectrum can't conform, please file a bug.

In the code, the result of c/parse-spec are called `spect` rather than
`spec`, just to differentiate the implementation. Spects convey
exactly the same information, but are more data-driven. Spects are
defrecords, so it's easy to assoc, dissoc, merge, etc types, which
we'll take advantage of.

### spectrum.flow

Flow is an intermediate pass. It takes the output of tools.analyzer,
analyzes function parameters and let bindings, and updates the
analyzer output with the appropriate spects. The main thing it's
responsible for is adding `::flow/ret-spec`, and any other useful
annotations to every expression. For example:

```clojure
(s/fdef foo :args (s/cat :x int?) :ret int?)
(defn foo [x]
  (let [y (inc x)]
    y))
```

Because foo has a spec, we destructure the arguments vector, and
assign the spec `#'int?` to `x`. In the `let`, we identify inc takes
an integer (handwaving here) and returns an int, and so assign `y` the
spec `int?`. Finally, the `y` in the body has the same spec as the y
in the `let`.

### spectrum.check

Where the magic happens. It takes a flow, and performs checks. Returns a seq of ParseError records.

## Transformers

clojure.spec doesn't have logic variables, which means some specs
aren't as tight as they could be. Consider `map`, which takes a fn of
one argument of type `X`, and returns a type `Y`, and a collection of
`X`s, and returns a seq of `Y`s ([X->Y] [X]->[Y]). That's currently impossible to
express in clojure.spec, the best we can do is specify the return type
of map as `seq?`, with no reference to `seq of Y`, which is based on
the return type of the mapping function.

Spectrum introduces spec transformers. They are hooks into the
checking process. For example,

```clojure
(ann #'map (fn [fnspec argspec]...))
```

ann takes a var, and a fn of two arguments, the original fnspec, and
the arguments to a particular invocation of the function. The
transformer should return an updated fnspec, presumably with the more
specific type. In this example, it would `clojure.core/update` the
`:ret` spec from `seq?` to `(coll-of y?)`. Since map also requires the
input type of `f` match the type of the seq passed in, we can
similarly update the expected type of the second argument in
`:arg`. Transforming happens before checking, so if the type becomes
more strict, that new value will be used when checking.

### value

In some cases, we can identify the type of an expression at compile time. For example,

```
(s/fdef foo :args (s/cat :x int?) :ret keyword?)
(defn foo [x]
  (if (int? x)
    :foo
    "bar"))

If we didn't know the value of the `if` test, the return spec of the `if`
expression would be `(or keyword? string?)`. The type for `int?` is
`any? -> boolean?`, which normally means we couldn't predict which
branch to take.  Using a spec transformer, we can make int? more
specific

Spect defines an instance transformer for int?:
```
(ann #'int? (instance-or [Long Integer Short Byte]))
```

In this case, `instance-or` is a higher-order function returning a
transformer that checks for the argument being an instance of any of
the specified classes. If we know the type of the argument passed to
`int?` at compile time, and it conforms, the spec transformer returns
`(value true)`. `value` is a spec unique to spectrum, which indicates a
literal value. `(value true)` represents this expression will always
return true, rather than boolean?, which could indicate true or false.

Some expressions, such as `if`, recognize `(value true)` and will
replace the type of the `if` expression from `(or keyword? string?)`
to just `keyword?`. Similarly, returning `(value false)` or `(value
nil)` will cause the code to take the else branch.

## Unknown

Spectrum doesn't insist that every var be spec'd immediately. There is
a specific spec, `unknown` used in places where we don't know type,
for example as the return value of an un-spec'd function. Passing
unknown to a spec'd function is treated as a less severe error than a
'real' type error, for example passing an int to a function expecting
keyword?. Use configuration, described in the next section, to remove
unknowns if desired.

The return value of un-spec'd functions is `unknown`, and in general,
unknown does not conform to any spec except `any?`.

## Configuration

Spectrum has configurable warning levels. Every check 'error' has
:type and :level, indicating the kind of error, and the author's
perceived importance of that error, for convenient
filtering/whitelisting/blacklisting. In general, the severity level of
an issue depends on how certain we are it will cause problems.

The error levels are:

- 0: informational
- 1: warning
- 2: error

errors

- 2 calling a fn with incorrect number of args (spec'd or not)
- 2 calling a spec'd fn with incompatible type (no unknown)
- 2 attempt to invoke a non-fn var (i.e. `(*print-level* 2)`)
- 2 spec arity doesn't conform to fn arity
- 2 return value of a spec'd fn doesn't conform
- 2 return value of a spec'd fn is unknown
- 2 calling a java method incompatible args

- 1 calling a spec'd fn with `unknown` args
- 1 calling a java method with unknown args

- 0 non-spec'd defn in a namespace being checked
- 0 fdef spec with no :ret

non-errors:
things spec won't warn about
- calling a non-spec'd fn from a non-spec'd fn

## Todo

- 100% coverage of all types returned by the analyzer
- 100% spec coverage
- pre/post post predicates
- java methods are all (or nil?)
- `updating` the type of variables in a recur
- s/def, but for non-fn vars

## Justification

- because I could
- working example of types = proofs = predicates
- this is extra checking on top of spec, not a replacement for it
- to get HN to shut up about how adding a static type system to a dynamic language is impossible
- why not just use spec by itself?
 - `instrument` doesn't check return values
 - `check` works best on pure functions with good generators.
  - Not all clojure code is pure
  - Not always easy to write a good generator for all functions (hello, any fn that takes a DB connection)
  - Not always easy to write a generator w/ 100% coverage
 - spec doesn't deal with non-fn vars at all (binding, alter-var-root, set!, etc)
 - generative testing can be slow

## Downsides

- spectrum is 'viral'. Once you start checking, it encourages you to write specs for everything


## License

Copyright © 2016 Allen Rohner

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
