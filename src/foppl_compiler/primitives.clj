(ns foppl-compiler.primitives
  (:use [anglican core emit runtime])
  (:require [clojure.core.matrix :as m])
  (:require [anglican.runtime :refer [tanh]]))

(use 'clojure.walk)

(defn append [& args] (apply conj args))

(defn mat-mul [& args] (apply m/mmul args))
(defn mat-add [& args] (apply m/add args))
(defn mat-transpose [& args] (apply m/transpose args))
(defn mat-tanh [M] (m/emap tanh M))
(defn mat-relu [M] (m/emap (fn [x] (if (> x 0) x 0)) M))
(defn mat-repmat [M r c]
  (let [R (reduce (partial m/join-along 0) (repeat r M))]
    (reduce (partial m/join-along 1) (repeat c R))))

(def ^:dynamic *primitive-procedures*
  "primitive procedures, do not exist in CPS form"
  (let [;; higher-order procedures cannot be primitive
        exclude '#{loop
                   map reduce
                   filter keep keep-indexed remove
                   repeatedly
                   every? not-any? some
                   every-pred some-fn
                   comp juxt partial}
        ;; runtime namespaces
        runtime-namespaces '[clojure.core anglican.runtime proto-repl-demo.primitives]]
    (set (keep (fn [[k v]]
                 (when (and (not (exclude k))
                            (fn? (var-get v)))
                   k))
               (mapcat ns-publics runtime-namespaces)))))
