## Changelog
- 0.1.4
  - major refactoring of flow (internal only)
  - removed c/spec->class, implement in terms of dependent-specs
  - improved java interop
  - improved primitive handling
  - improved numeric tower
  - check deftype/defrecord protocol implementations
  - adds NotSpec
  - numerous bug fixes
- 0.1.3
  - add support for s/tuple
  - make 'Invoke' first class.
  - Move invoke checking into flow
  - simplify several anns to use Invoke directly, making it easier to
    ann `map` & `filter`
  - start using spects rather than clojure.spec special-cases in more
    places (::s/nil, use fewer naked values, etc)
  - better support for KeywordInvoke and Invoke on maps and values
  - `conform` now performs a breadth first search, which helps with recursive dependent specs

- 0.1.2
  - adds type-of
  - better `if` branch detection
  - handle more clojure.specs
  - lots of bug fixes

- 0.1.1
  - multispec support
  - parse-spec is now lazy, recursive specs should work
  - 150 more commits worth of stuff
  - spectrum.check/analyze-form
  - spectrum.check/check-form

- 0.1.0 First release
