
[![Clojars Project](https://img.shields.io/clojars/v/spectrum.svg)](https://clojars.org/spectrum) [![CircleCI](https://circleci.com/gh/arohner/spectrum/tree/master.svg?style=svg)](https://circleci.com/gh/arohner/spectrum/tree/master)

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
- readable implementation
- fast
- configurable strictness levels
- incremental checking

## Non-goals

- perfection
- correctness
- requiring 100% spec coverage.

In particular, spectrum aims to be fast and usable, and catching
bugs. It aims to have low false positives, at the expense of
potentially not catching 100% of type errors.

A tool that catches 80% of bugs that you use every day is better
than a 100% tool that you don't use. Spectrum will converge on 100% correct,
but won't guarantee correctness for a while.

## Usage

Use clojure.spec as normal. Then, at the repl or during tests:

```clojure
(require '[spectrum.check :as check])

(check/check 'your.namespace)
```

Returns a seq of Error defrecords.

There is also

```clojure
(:spectrum.flow/ret-spec (check/analyze-form '(map inc (range 5))))
```
which is useful when you want to debug the signature of a form.

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

- It's still very early. Contributions welcome.


## How It Works

This section is for the curious, and potential contributors. Shouldn't be necessary to understand this to use spectrum.

### spectrum.conform

This contains a spec parser and a re-implementation of clojure.spec, except they work on literals and specs rather than normal clojure values.

```clojure
(:require [spectrum.conform :as c])
(c/conform (s/cat :x integer?) [3])
=> {:x 3}
```

```clojure
(c/parse-spec (s/+ integer?))
```

Returns a defrecord, containing the parsed spec. This is basically a
reimplementation of clojure.spec, except more data-driven. If you're
not using spectrum, but want to do other analysis-y stuff with specs,
you may find `spectrum.conform/parse-spec` useful.

```clojure
(c/conform (s/+ integer?) [1 2 3])

(c/conform (s/+ integer?) '[integer? integer?])
```

`c/conform` behaves the same as `s/conform`, except it works on
literals and specs (i.e. the things we have access to at compile
time). For now, the best documentation is the tests,
`test/spectrum/conform_test.clj`. Spectrum conform will have 100%
coverage of clojure.spec, but isn't done yet. If you encounter a spec
that spectrum can't `c/parse-spec`, please file a bug.

In the code, the result of `c/parse-spec` are called `spect` rather
than `spec`, just to differentiate the implementation. Spects convey
exactly the same information, but are defrecords, so it's easy to
assoc, dissoc, merge, etc types, which we'll take advantage of.

### spectrum.flow

Flow is an intermediate pass. It takes the output of tools.analyzer,
and recursively walks the analysis, adding specs to every
expression. The main thing it's responsible for is adding
`::flow/ret-spec`, and any other useful annotations to every
expression. For example:

```clojure
(s/fdef foo :args (s/cat :x int?) :ret int?)
(defn foo [x]
  (let [y (inc x)]
    y))
```

Because foo has a spec, we destructure the arguments vector, and
assign the spec `#'int?` to `x`. In the `let`, we identify inc takes
an long and returns a long, and so assign `y` the
spec `long`. Finally, the `y` in the body has the same spec as the y
in the `let`.

### spectrum.check

Where the magic happens. It takes a flow, and performs checks. Returns a seq of ParseError records.

The checking process just `c/conform`s the inputs to every function
call, and the return value of functions. Using our previous example,
`y` has the spec `(c/and (c/value 3) (c/class Long))`, and (c/conform
#'int? x) returns truthy, so the function checks.

## Transformers

Spectrum has two kinds of transformers, to add more detail to types: invoke transformer and type transformer

### Invoke

clojure.spec doesn't have logic variables, which means some specs
aren't as tight as they could be. Consider `map`, which takes a fn of
one argument of type `X`, and returns a type `Y`, and a collection of
`X`s, and returns a seq of `Y`s ([X->Y] [X]->[Y]). That's currently impossible to
express in clojure.spec, the best we can do is specify the return type
of map as `seq?`, with no reference to `seq of Y`, which is based on
the return type of the mapping function.

Spectrum introduces transformers. They are hooks into the
checking process. For example,

```clojure
(ann #'map (fn [fnspec argspec]...))
```

ann takes a var, and a fn of two arguments, the original fnspec, and
the arguments to a specific invocation of the function (map). The
transformer should return an updated fnspec, presumably with the more
specific type. In this example, it would `clojure.core/update` the
`:ret` spec from `seq?` to `(coll-of y?)`. Since map also requires the
input type of `f` match the type of the seq passed in, we can
similarly update the expected type of the second argument in
`:arg`. The updated spec will be used in place during the normal checking process.

Invoke transformers are only run when checking a function invokation.

#### type transformers

Type transformers are a second kind of hook, used to attach additional
specs to *values* during the checking process. Consider

```clojure
(s/fdef foo :args (s/cat :x map?))

(defn foo [x]
  (seq x))
```

Is this call legal? It is, but the `map?` predicate by itself doesn't
indicate that maps are seqable. We know `seq` should work on anything
where `seqable?` returns true, and from reading Clojure's
implementation, we know seq will accept values that are `(instance?
Map %)` (defined in `clojure.lang.RT/seqFrom`, if you're curious). We
can and do use an instance transformer for `(seq)` and `(seqable?`),
but those don't help us in the situation where `seqable?` isn't the
function being invoked. Continuing our example:

```clojure
(s/fdef foo :args (s/cat :x map?))
(s/fdef bar :args (s/cat :y seqable?))

(defn foo [x]
  (bar x))
```

We know this should pass, because maps are seqable?, but the predicate
only gets us so far. Type transformers are used to attach additional
specs to to values during the checking process. In this case, we add a
type transformer to `seqable?` to specify values that are `seqable?` also have the spec `(or clojure.lang.ISeq java.util.Map <bunch of other classes>)`.
The call to `bar` now checks, because passing a map to a spec expecting
`(or java.util.Map...)` conforms.

For the most part, you shouldn't need to use type transformers,
because they are primarily used to flesh out operations in the Clojure
implementation.

## Unknown

Spectrum doesn't insist that every var be spec'd immediately. There is
a specific spec, `c/unknown` used in places where we don't know type,
for example as the return value of an un-spec'd function. Passing
unknown to a spec'd function is treated as a less severe error than a
'real' type error, for example passing an `int` to a function expecting
`keyword?`. Use configuration, described in the next section, to remove
unknowns if desired.

The return value of un-spec'd functions is `unknown`, and in general,
unknown does not conform to any spec except `any?`.

## Configuration

(Planned. TBD. Didn't mean to commit this, leaving for informational purposes)

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


## Changelog

- 0.1.1
  - multispec support
  - parse-spec is now lazy, recursive specs should work
  - 150 more commits worth of stuff
  - spectrum.check/analyze-form
  - spectrum.check/check-form

- 0.1.0 First release

## License

Copyright © 2016 Allen Rohner

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
