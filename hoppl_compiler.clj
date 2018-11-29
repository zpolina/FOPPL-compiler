(ns foppl-compiler.hoppl-compiler
  (:require [foppl-compiler.core :refer :all]
            [clojure.set :as set]
            [clojure.pprint :as pprint]
            [anglican.runtime :refer :all]
            [foppl-compiler.desugar :refer [desugar]]
            [foppl-compiler.substitute :refer [substitute]]
            [foppl-compiler.partial-evaluation :refer [partial-evaluation]]
            [foppl-compiler.symbolic-simplify :refer [symbolic-simplify]]
            [foppl-compiler.primitives :refer :all]
            [foppl-compiler.analyze :refer [analyze empty-env empty-graph]]
            [foppl-compiler.free-vars :refer [free-vars]]
            [anglican.runtime :refer [observe* normal sample* uniform-continuous mvn mean std]])
            (:use [anglican core emit runtime]
                [clojure.walk]
                [clojure.pprint]))

(def ^:dynamic *primitive-procedures*
  "primitive procedures for Anglican semantics" ;; TODO check implications of this choice
  (let [;; higher-order procedures cannot be primitive
        exclude '#{loop
                   map reduce
                   filter keep keep-indexed remove
                   repeatedly
                   every? not-any? some
                   every-pred some-fn
                   comp juxt partial}
        ;; runtime namespaces
        runtime-namespaces '[clojure.core anglican.runtime foppl-compiler.primitives]]
    (set (keep (fn [[k v]]
                 (when (and (not (exclude k))
                            (fn? (var-get v)))
                   k))
               (mapcat ns-publics runtime-namespaces)))))


(def ^:dynamic *bound*
 (into *primitive-procedures* ['if 'let]))


(defn rho [exp]
 (into {} (for [func exp
       :when (and (coll? func) (= 'defn (first  func)))
       :let [rho-map {(second func) {:vars (nth func 2) :exp (nth func 3)}}]]
       rho-map)))

(defn exp-extract [exp]
 (if (and (coll? exp) (coll? (first exp)) (= (first (first exp)) 'defn))
   (last exp)
   exp))






;; do not replace values when it is let within

(defn eval-hoppl [exp, sigma, l, rho, prims]
 (if (coll? exp)
   (cond
     (vector? exp)
       (let [new_exp (conj (seq exp) 'vector)]
             (eval-hoppl new_exp sigma l rho prims))
     (map? exp)
       (let [new_exp (conj (seq (into [] cat exp)) 'hash-map)]
             (eval-hoppl new_exp sigma l rho prims))
     (= (first exp) 'let)
       (let [pair (eval-hoppl (second (second exp)) sigma l rho prims)
             c_1  (first pair)
             sigma  (second pair)
             v1 (first (second exp))
             l (assoc l v1 c_1 )]
             (eval-hoppl (nth exp 2) sigma l rho prims))
     (= (first exp) 'if)
       (let [pair (eval-hoppl (second exp) sigma l rho prims)
             e_1  (first pair)
             sigma  (second pair)]
             (if (true? e_1)
                 (eval-hoppl (nth exp 2) sigma l rho prims)
                 (eval-hoppl (nth exp 3) sigma l rho prims)
             ))
     (= (first exp) 'sample)
       (let [pair (eval-hoppl (second exp) sigma l rho prims)
             e_1  (first pair)
             sigma  (second pair)]
             [(sample* e_1) sigma])
     (= (first exp) 'observe)
     (let [pair (eval-hoppl (second exp) sigma l rho prims)

           d_1  (first pair)
           sigma  (second pair)
           pair (eval-hoppl (nth exp 2) sigma l rho prims)
           c_2  (first pair)
           sigma  (second pair)
           sigma (+ sigma (observe* d_1 c_2))]
           [c_2 sigma])
     (= (first exp) 'fn)
       (if (vector? (second exp))
         ()
         (let [ exp {:vars (nth exp 2) :exp (nth exp 3)}]
                   [exp sigma])
       )
       (= (first exp) 'reduce)
        (let [first_arg (first (eval-hoppl (nth exp 2) sigma l rho prims))
             second_arg (first (eval-hoppl (nth exp 3) sigma l rho prims))
             func (second exp)
             func {:vars (nth func 1) :exp (nth func 2)}]
             (loop [ x first_arg
                     y second_arg
                     func func
                     sum_sigma sigma]
                  (if (empty? y)
                      [x sum_sigma]
                      (let [m (zipmap (func :vars) [x (first y)])
                            l (merge l m)
                            [v s] (eval-hoppl (func :exp) sum_sigma l rho prims)]
                          (recur v (rest y) func s)
                      )
                  )
        ))
     (contains? l (first exp))
        (let [nexp (l (first exp))
              vars (nexp :vars)
              nexp (nexp :exp)
              vals_sigmas (for [e (rest exp)]
                          (eval-hoppl e sigma l rho prims))
              sigma (sum (into [] (map second vals_sigmas)))
              vals (map first vals_sigmas)
              vvals (into [] vals)
              new_ls (zipmap vars vvals)
              l (merge l new_ls)]
              (eval-hoppl nexp sigma l rho prims))
     (contains? rho (first exp))
       (let [nexp (rho (first exp))
             vars (nexp :vars)
             nexp (nexp :exp)
             vals_sigmas (for [e (rest exp)]
                         (eval-hoppl e 0.0 l rho prims))
             sigma (+ sigma (sum (into [] (map second vals_sigmas))))
             vals (map first vals_sigmas)
             vvals (into [] vals)
             new_ls (zipmap vars vvals)
             l (merge l new_ls)]
             (eval-hoppl nexp sigma l rho prims))
     (contains? prims (first exp))
       (let [
             vars_sigmas (for [e (rest exp)]
                         (eval-hoppl e 0.0 l rho prims))
             sigma (+ sigma (sum (into [] (map second vars_sigmas))))
             vars (map first vars_sigmas)
             vvars (into [] vars)]
                         [(apply (resolve (first exp)) vvars) sigma])
     :else
       nil)
   (if (number? exp)
     [exp, sigma]
     [(l exp) sigma])))





 (defn weighted_sum [samples]
   (let [vals (into [] (map first samples))
         sigmas (into [] (map exp (map second samples)))
         up (sum (mapv * vals sigmas))
         down (sum sigmas)
         ]
         (/ up down)))



 (defn weighted_sum_2 [samples]
   (loop [x 0
         res []
         samples samples]
     (if (> x 16 )
         res
         (let [ vals (into [] (map #(nth (first %) x) samples))
                sigmas (into [] (map exp (map #(second %) samples)))
                up (sum (mapv * vals sigmas))
                down (sum sigmas)]
                (recur (+ x 1) (conj res (/ up down)) samples))
     )
   )
 )






(defn eval-final [desug-exp rho]
  (lazy-seq
  (let [sample (eval-hoppl desug-exp 0.0 {} rho *primitive-procedures*)]
    (cons sample (eval-final desug-exp rho))))
)


(def program1 '((let [p 0.01
              dist (flip p)
              until-success (fn until-success [p n]
                               (if (sample dist)
                                 n
                                 (until-success p (+ n 1))))]
             (until-success p 0))))


(let [samples (take 1000 (eval-final (first (exp-extract (map desugar program1))) {} ))]
                     (weighted_sum samples))



(def program2 '((defn marsaglia-normal [mean var]
  (let [d (uniform-continuous -1.0 1.0)
        x (sample d)
        y (sample d)
        s (+ (* x x ) (* y y ))]
          (if (< s 1)
            (+ mean (* (sqrt var)
                       (* x (sqrt (* -2 (/ ( log s) s))))))
            (marsaglia-normal mean var))))

(let [mu (marsaglia-normal 1 5)
      sigma (sqrt 2)
      lik (normal mu sigma)]
  (observe lik 8)
  (observe lik 9)
  mu)))


(let [samples (take 100000 (eval-final (exp-extract (map desugar program2)) (rho (map desugar program2))))]
                     (weighted_sum samples))







(def program3 '((let [observations [0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1 0.0 0.13 0.45 6 0.2 0.3 -1 -1]
      init-dist (discrete [1.0 1.0 1.0])
      trans-dists {0 (discrete [0.1 0.5 0.4])
                   1 (discrete [0.2 0.2 0.6])
                   2 (discrete [0.15 0.15 0.7])}
      obs-dists {0 (normal -1 1)
                 1 (normal 1 1)
                 2 (normal 0 1)}]
      (reduce
        (fn [states obs]
          (let [state (sample (get trans-dists
                                   (peek states)))]
            (observe (get obs-dists state) obs)
            (conj states state)))
        [(sample init-dist)]
        observations))))



(let [samples (take 100000 (eval-final (first (exp-extract (map desugar program3))) {} ))]
                      (weighted_sum_2 samples))
