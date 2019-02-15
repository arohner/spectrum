(ns spectrum.util
  (:require [clojure.tools.analyzer.jvm :as ana.jvm]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [orchestra.spec.test :as ost])
  (:import clojure.lang.Var
           java.lang.System))

(defn literal? [x]
  (let [a (ana.jvm/analyze x)]
    (and (:literal? a) (not= :unknown (:type a)))))

(defn fn-literal? [x]
  (and (seq? x)
       (= 'fn* (first x))
       (let [a (ana.jvm/analyze x)]
         (= :fn (:op a)))))

(s/fdef var-name :args (s/cat :v var?) :ret symbol?)
(defn var-name [^Var v]
  (symbol (str (.ns v)) (str (.sym v))))

(s/fdef strip-namespace :args (s/cat :k keyword?) :ret simple-keyword?)
(defn strip-namespace [k]
  (keyword (name k)))

(defn zip
  "Returns (get x key), with x attached as metadata"
  [a key]
  (let [v (get a key)]
    (assert v)
    (with-meta v {:a a})))

(defn with-a [x a]
  (with-meta x {:a a}))

(defn unwrap-a [x]
  (-> x meta :a))

(defn unwrap-while [x f]
  (let [a (unwrap-a)]
    (when a
      (if (f a)
        a
        (recur a f)))))

(defn print-once* [& args]
  (apply println args))

(def print-once (memoize print-once*))

(s/fdef protocol? :args (s/cat :x any?) :ret boolean?)
(defn protocol? [x]
  (and (map? x)
       (var? (:var x))
       (class? (:on-interface x))
       (map? (:method-map x))))

(s/fdef namespace? :args (s/cat :x any?) :ret boolean?)
(defn namespace? [x]
  (instance? clojure.lang.Namespace x))

(s/fdef queue? :args (s/cat :x any?) :ret boolean?)
(defn queue? [x]
  (instance? clojure.lang.PersistentQueue x))

(s/fdef queue :args (s/cat :coll (s/? coll?)) :ret queue?)
(defn queue
   ([] clojure.lang.PersistentQueue/EMPTY)
   ([coll] (reduce conj clojure.lang.PersistentQueue/EMPTY coll)))

(defn conj-seq [x coll]
  (reduce (fn [x a]
            (conj x a)) x coll))

(defmethod print-method clojure.lang.PersistentQueue
  [q ^java.io.Writer w]
  (.write w "#queue ")
  (print-method (sequence q) w))

(defn var-sym [^Var v]
  (symbol (str (.name (.-ns v))) (str (.-sym v))))

(defmacro predicate-spec
  "fdef name any? -> boolean?"
  [x]
  (let [sym (cond
              (var? x) (var-sym x)
              (symbol? x) x
              :else (assert false)) ]
    `(s/fdef ~sym :args (s/cat :x any?) :ret boolean?)))

(defmacro def-instance-predicate
  "(defn name [x] (instance? cls x))"
  [name cls]
  `(do
     (defn ~name [x#]
       (instance? ~cls x#))
     (predicate-spec ~name)))

(defn validate! [s args & [extra-data]]
  (or
   (s/valid? s args)
   (throw (ex-info (s/explain-str s args)
                   {:spec s
                    :args args
                    :data (merge extra-data (s/explain-data s args))}))))

(defn multimethod-dispatch-values
  "Returns the seq of allowed dispatch values in the multimethod"
  [^clojure.lang.MultiFn ms]
  (->> (.getMethodTable ms)
       (keys)))

(defn instrument-in-CI []
  (when (System/getenv "CI")
    (stest/instrument)))

(defn instrument-ns
  "Instrument all vars in ns, or *ns*"
  ([]
   (instrument-ns *ns*))
  ([ns]
   (s/check-asserts true)
   (->> ns
        (ns-publics)
        (vals)
        (mapv (fn [v]
                (symbol (str (.ns v) "/" (.sym v)))))
        (ost/instrument)
        (dorun))))

(defn memoize-with
  "Memoize `f`, using (keyfn args) as the cache key"
  [keyfn f]
  (let [mem (atom {})]
    (fn [& args]
      (let [k (apply keyfn args)]
        (if-let [e (find @mem k)]
          (val e)
          (let [ret (apply f args)]
            (swap! mem assoc k ret)
            ret))))))

(def-instance-predicate url? java.net.URL)
(def-instance-predicate namespace? clojure.lang.Namespace)

(defmacro defn-memo
  "Just like defn, but memoizes the function using clojure.core/memoize"
  [fn-name & defn-stuff]
  `(do
     (defn ~fn-name ~@defn-stuff)
     (alter-var-root (var ~fn-name) memoize)
     (var ~fn-name)))

(defmacro time-when
  "clojure.core/time, but only print when elapsed time took longer than `timeout`"
  [timeout expr]
  `(let [start# (. System (nanoTime))
         ret# ~expr
         elapsed# (/ (double (- (. System (nanoTime)) start#)) 1000000.0)]
     (when (> elapsed# ~timeout)
       (prn (str (quote ~expr) "Elapsed time: " elapsed# " msecs")))
     ret#))

(defn multimethod-dispatch-values
  "Returns the seq of allowed dispatch values in the multimethod"
  [^clojure.lang.MultiFn ms]
  (->> (.getMethodTable ms)
       (keys)))

(defn private-method
  "Calls a private or protected method.

   class - the class where the method is declared
   params - a vector of Class which correspond to the arguments to the method
   obj - nil for static methods, the instance object otherwise
   method-name - something Named"
  [class method-name params obj & args]
  (-> class (.getDeclaredMethod (name method-name) (into-array Class params))
    (doto (.setAccessible true))
    (.invoke obj (into-array Object args))))

(defn dominates?
  "True if dispatch value x dominates dispatch value y on multimethod mm"
  [mm x y]
  (-> (private-method clojure.lang.MultiFn :dominates [Object Object] mm x y)
      (str)
      (Boolean/getBoolean)))

(defn debug-multimethod-dispatch
  "Given the arguments to call a multimethod with, print debugging information about why a method was chosen"
  [mm args]
  (let [dispatch-fn (.dispatchFn mm)
        dispatch-val (apply dispatch-fn args)
        default (.defaultDispatchVal mm)
        method-table (.getMethodTable mm)
        hierarchy (deref (.hierarchy mm))]
    (println "dispatch-val:" dispatch-val)
    (->> method-table
         (reduce (fn [best entry]
                   (let [ek (.getKey entry)
                         bk (when best (.getKey best))]
                     (if (isa? hierarchy dispatch-val ek)
                       (if (or (nil? best) (dominates? mm ek bk))
                         (do
                           (println ek ">" bk)
                           entry)
                         best)
                       best))) nil)
         ((fn [best]
            (if (nil? best)
              (println "best=nil, default:" default)
              (key best)))))))
