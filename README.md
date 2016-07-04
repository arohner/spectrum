# spectrum

A library for catching clojure.spec errors at compile time.

**Wait what?**

It's like core.typed, but it relies on clojure.spec annotations.

**So it's an optional static type system?**

Kind-of. It finds errors at compile time, and predicates kind of look like types. So sure.

![Proving contracts ahead of time](https://pbs.twimg.com/media/CjcVSAVUYAIBY3Z.jpg)


## Usage

```clojure
(require '[spectrum.check :as st])

(st/check-ns 'foo.bar)
```

Returns a seq of Error defrecords.

## Goals

- usable
- pragmatic
- readable code
- fast
- configurable strictness levels

## Non-goals

- perfection
- correctness

## Limitations

- It's still very early. It doesn't understand all clojure forms yet, nor all spec annotations. Contributions welcome.

- It only proves things that your specs would have caught, not that the function has no type errors.

- It also proceeds from the assumption that your specs are correct (i.e. no spec errors at runtime). If you're not running clojure.test.spec or not running your unit tests with `instrument`, you're gonna have a bad time.


## How It Works

This section is for the curious, and potential contributors. Shouldn't be necessary to understand this to use it.

### spectrum.conform

This contains a spec parser and a re-implementation of clojure.spec regexes, except they work on literals and symbols rather than normal clojure values.

```clojure
(require '[spectrum.conform :as c])
(c/parse-spec (s/+ integer?))
```
Returns a defrecord, containing the parsed spec. This is basically a reimplementation of clojure.spec, except more data-driven. If you're not using spectrum, but want to do other analysis-y stuff with specs, you may find this useful.

```
(c/conform (c/parse-spec (s/+ integer?)) [1 2 3])

(c/conform (c/parse-spec (s/+ integer?)) (c/parse-spec '[integer? integer?]))
```

`c/conform` behaves the same as `s/conform`, except it works on literals and specs (i.e. the things we have access to at compile time)

### spectrum.flow

Flow is an intermediate pass. It takes the output of tools.analyzer, analyzes function parameters and let bindings, and updates the analyzer output with the appropriate specs, to make checking simpler. The main thing it's responsible for is adding a :spectrum.flow/spec to every expression.

### spectrum.check

Where the magic happens. It takes a flow, and performs checks. Returns a seq of ParseError records.

## Todo

- flow specs through let
- hook into require
- map invoke
- `(if predicate then else)` forms
- pre/post post predicates

## Future work

There are things core.typed can prove, that clojure.spec currently
can't. Spectrum should be able to recognize known
higher order functions, like `clojure.core/map`. We know the type of
`map` is `[[X -> Y] (Seq X) -> (Seq Y)]`. That is, map takes a `fn`
that takes X and returns Y, and a seq of Xs, and returns a seq of
Y. Currently, the best `clojure.spec` can do is say `:ret (seq-of
::s/any)`

The current plan is to write spec-transformer functions. These are
functions that take 1) a var, 2) its existing spec, 3) the spec of the
arguments and returns an updated spec.

## License

Copyright © 2016 Allen Rohner

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
