[![CircleCI](https://circleci.com/gh/arohner/spectrum.svg?style=svg)](https://circleci.com/gh/arohner/spectrum)
[![Clojars Project](https://img.shields.io/clojars/v/spectrum.svg)](https://clojars.org/spectrum)

# spectrum

A library for doing static analysis of Clojure code, catching clojure.spec conform errors at compile time.

**Wait what?**

It's like core.typed, but it relies on clojure.spec annotations.

**So it's an optional static type system?**

Kind-of. It finds errors at compile time, and predicates kind of look like types. So sure.

![Proving contracts ahead of time](https://pbs.twimg.com/media/CphGpB5VUAAJyGL.jpg)

## Current Status

Developer Preview, not yet ready for production use.

Current development is working towards making spectrum self-check.

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
(check/type-of '(map inc (range 5)))
```
which is useful when you want to debug the signature of a form.

`type-of` can optionally also take a map of keywordized variables to spects

```clojure
(check/type-of '(string? x) {:x (c/pred-spec #'string?)})
#Value[true]

(check/type-of '(string? x) {:x (c/value 3)})
#Value[false]
```

## Limitations

- It's still very early. Contributions welcome.

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

## Plan

Spectrum is still very early, and not ready for production use. Current development is focused on making spectrum self-check.

## License

Copyright © 2016 Allen Rohner

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
