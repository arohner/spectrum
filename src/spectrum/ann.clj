(ns spectrum.ann
  (:require [clojure.spec :as s]
            [spectrum.conform :as c]
            [spectrum.data :as data]))

(s/def ::transformer (s/fspec :args (s/cat :spec ::c/spect :args-spec ::c/spect) :ret ::c/spect))

(s/fdef register-spec-transformer :args (s/cat :v var? :f ::transformer))
(defn register-spec-transformer
  "Register a spec transformer. Takes a var, and a transformer function

transformer function: a function taking 2 args: the function's spect, and the Spect for the fn args at this callsite. Returns an updated spec. Updating the :ret is probably a good idea. When types can be determined statically, consider returning (c/val true) and (c/val false)
"
  [v f]
  (swap! data/spec-transformers assoc v f)
  nil)

(def ann register-spec-transformer)

(defn instance-transformer
  "Returns a spec-transformer for a simple (instance? c x) spec."
  [cls]
  (fn [spect args-spect]
    (let [c (c/spec->class (c/first* args-spect))]
      (if c
        (if (isa? c cls)
          (assoc spect :ret (c/value true))
          (assoc spect :ret (c/value false)))))))

(def pred->class
  {#'associative? clojure.lang.Associative
   #'bigdec java.math.BigDecimal
   #'boolean? Boolean
   #'char? Character
   #'chunked-seq? clojure.lang.IChunkedSeq
   #'class? Class
   #'coll? clojure.lang.IPersistentCollection
   #'counted? clojure.lang.Counted
   #'decimal? BigDecimal
   #'delay? clojure.lang.Delay
   #'double? Double
   #'fn? clojure.lang.Fn
   #'future? java.util.concurrent.Future
   #'ifn? clojure.lang.IFn
   #'indexed? clojure.lang.Indexed
   #'inst? java.util.Date
   #'keyword? clojure.lang.Keyword
   #'list? clojure.lang.IPersistentList
   #'map-entry? java.util.Map$Entry
   #'map? clojure.lang.IPersistentMap
   #'number? Number
   #'ratio? clojure.lang.Ratio
   #'reader-conditional? clojure.lang.ReaderConditional
   #'reversible? clojure.lang.Reversible
   #'seq? clojure.lang.ISeq
   #'sequential? clojure.lang.Sequential
   #'set? clojure.lang.IPersistentSet
   #'sorted? clojure.lang.Sorted
   #'string? String
   #'symbol? clojure.lang.Symbol
   #'tagged-literal? clojure.lang.TaggedLiteral
   #'uri? java.net.URI
   #'uuid? java.util.UUID
   #'var? clojure.lang.Var
   #'vector? clojure.lang.IPersistentVector
   #'volatile? clojure.lang.Volatile
   })

(doseq [[v cls] pred->class]
  (data/register-pred->class v cls)
  (register-spec-transformer v (instance-transformer cls)))

(ann #'not (fn [spect args-spec]
             (println "ann #'not:" spect args-spec)
             (let [arg (c/first* args-spec)]
               (if (c/value? arg)
                 (if (:v arg)
                   (assoc spect :ret (c/value false))
                   (assoc spect :ret (c/value true)))
                 spect))))
