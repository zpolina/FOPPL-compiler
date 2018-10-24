(ns foppl-compiler.hmc
  (:require [foppl-compiler.core :refer :all]
            [clojure.set :as set]
            [clojure.core.matrix :as M]
            [foppl-compiler.reverse-diff :refer :all]
            [foppl-compiler.desugar :refer [desugar]]
            [foppl-compiler.substitute :refer [substitute]]
            [foppl-compiler.partial-evaluation :refer [partial-evaluation]]
            [foppl-compiler.symbolic-simplify :refer [symbolic-simplify]]
            [foppl-compiler.primitives :refer :all]
            [foppl-compiler.analyze :refer [analyze empty-env empty-graph]]
            [foppl-compiler.free-vars :refer [free-vars]]
            [anglican.runtime :refer [observe* normal sample* uniform-continuous mvn mean std]])
            (:use
                [clojure.walk]))


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


(defn evaled-desugared [program]
(let [pe (map partial-evaluation program)
      ss (map symbolic-simplify pe)]
      (map desugar ss)))

(defn make-map-return [exp]
  (let [fv (into [] (free-vars exp *bound*))]
      [(eval (list 'fn fv exp)) fv])
  )




(defn update-link [key exp]
  (if (= (first exp) 'sample*)
      (let [exp (pop (second exp))
            exp (conj exp key)]
            (conj exp 'normpdf)
       )
       (let [exp2 (pop (second exp))
             exp (conj exp2 (nth exp 2))]
             (conj exp 'normpdf)
       )
  ))



(defn make-U [inv-graph links]
 (loop [links links
       result-exp (list)
       depends-set (list)]
     (if (empty? links)
       [(list '* '(- 1)(conj result-exp '+)) (into [] (set depends-set))]
       (let [
           key-exp (first links)
           key (first key-exp)
           exp (second key-exp)
           depends (get inv-graph key)
           depends (into [] depends)
           upd-link (update-link key exp)
         ](recur (rest links) (conj result-exp upd-link) (concat depends-set depends))))
     )
 )

(defn hmc-prep [program]
 (let [graph (program->graph (evaled-desugared program))
       output (last graph)
       instr (graph->instructions graph)
       eval-instr (eval-instructions instr)
       graph (second graph)
       links (graph :P)
       X (into {} (drop-last eval-instr))
       vars (keys (graph :A))
       inv-graph (invert-graph (:A graph))
       return-map (make-map-return output)
       U (make-U inv-graph links)
       f (list 'fn (second U) (first U))
       depends (second U)
       diff (eval (apply reverse-diff* (rest f)))
       num-vars (count vars)
       means (M/matrix (vec (replicate num-vars 0)))
       M (M/identity-matrix num-vars)
       M-inv (M/inverse M)
       T 5
       eps 0.00001
       ]
       [links X vars return-map T eps means M M-inv diff depends]
   ))


(defn leapfrog [res bp X R T eps deriv vars depends]
 (loop [T T
        X X
        R1_2 (M/sub R (M/mul 0.5 (M/mul eps (bp 1.0))))]
    (if (= 0 T)
      [(zipmap depends (M/add (postwalk-replace X depends) R1_2))
       (M/sub R1_2 (M/mul 0.5 (M/mul eps ((second (apply deriv (postwalk-replace (zipmap depends (M/add (postwalk-replace X depends) R1_2)) depends))) 1.0))))]
      (let [
          Xt (M/add (postwalk-replace X depends) (M/mul eps R1_2))
          Xt (zipmap depends Xt)
          R1_2 (M/sub R1_2 (M/mul eps ((second (apply deriv (postwalk-replace Xt depends))) 1.0)))
        ]
        (recur (- T 1) Xt R1_2)
      )
   )
 )
)

(defn hmc-step [[links X vars evaled-output T eps means M M-inv deriv depends]]
 (lazy-seq
 (let [
      R (sample* (mvn means M))
      [res bp] (apply deriv (postwalk-replace X depends))
      lf (leapfrog res bp X R T eps deriv vars depends)
      X' (first lf)
      R' (second lf)
      u (sample* (uniform-continuous 0 1))
      K (M/mget (M/mmul 1/2 (M/mmul (M/mmul (M/transpose R) M-inv) R)))
      K' (M/mget (M/mmul 1/2 (M/mmul (M/mmul (M/transpose R') M-inv) R')))
      U (M/mget res)
      U' (M/mget (first (apply deriv (postwalk-replace X' depends))))
      alpha (exp (- (+ U K) (+ U' K')))
      sample  (if (< u alpha) X' X)
 ]
 (cons (postwalk-replace {true 1.0 false 0.0} (apply (first evaled-output)
 (postwalk-replace  sample (second evaled-output))))
 (hmc-step [links sample vars evaled-output T eps means M M-inv deriv depends])))
))

(defn hmc [program]
    (let [params (hmc-prep program)]
          (hmc-step params)))



(let [samples (take 100000 (drop 10000(hmc program1)))]
        (mean samples) )
(let [samples (take 200000 (drop 10000 (hmc program2)))]
        (mean samples))
(let [samples (take 500000 (drop 50000 (hmc program3)))]
        [(mean samples) (std samples)])




(def program1 '((let [mu (sample (normal 1 (sqrt 5)))
           sigma (sqrt 2)
           lik (normal mu sigma)]
       (observe lik 8)
       (observe lik 9)
       mu)))


(def program2 '((defn observe-data [_ data slope bias]
 (let [xn (first data)
       yn (second data)
       zn (+ (* slope xn) bias)]
   (observe (normal zn 1.0) yn)
   (rest (rest data))))

(let [slope (sample (normal 0.0 10.0))
     bias  (sample (normal 0.0 10.0))
     data (vector 1.0 2.1 2.0 3.9 3.0 5.3
                  4.0 7.7 5.0 10.2 6.0 12.9)]
 (loop 6 data observe-data slope bias)
 (vector slope bias))))



 (def program3 '((let [x (sample (normal 0 10))
       y (sample (normal 0 10))]
   (observe (normal (+ x y) 0.1) 7)
   [x y])))
