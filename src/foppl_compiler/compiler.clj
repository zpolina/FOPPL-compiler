(ns foppl-compiler.compiler
  (:require [foppl-compiler.desugar :as d]
            [foppl-compiler.primitives :as p]
            [foppl-compiler.graph :as graph])
  (:use [anglican core emit runtime]
        [clojure.walk]
        [clojure.pprint]))


;;Function for generating the rho-map, key is a fucntion name, body is another
;; with variables and with body
(defn rho [exp]
  (into {} (for [func exp
        :when (and (coll? func) (= 'defn (first  func)))
        :let [rho-map {(second func) {:vars (nth func 2) :exp (nth func 3)}}]]
        rho-map)))

(defn exp-extract [exp]
  (if (and (coll? exp) (coll? (first exp)) (= (first (first exp)) 'defn))
    (last exp)
    exp))

(defn subst-func [body vars exps]
  (postwalk-replace (zipmap vars exps) body))

(defn score [exp v]
  (if (coll? exp)
  (cond
    (= (first exp) 'if)
      (list 'if (second exp) (score (nth exp 2) v) (score (nth exp 3) v))
    (= (first exp) 'normal)
      (conj (conj (rest exp) v) 'normal-pdf)
    (= (first exp) 'uniform-continuous)
      (conj (conj (rest exp) v) 'uniform-continuous-pdf)
    (= (first exp) 'beta)
      (conj (conj (rest exp) v) 'beta-pdf)
    (= (first exp) 'bernoulli)
      (conj (conj (rest exp) v) 'bernoulli-pdf)
    (= (first exp) 'discrete)
      (conj (conj (rest exp) v) 'discrete-pdf)
  :else
     (conj exp v))
  (throw (Exception.
    "expression doesn't evaluate to a distribution constructor"))))

(def pdfs
  (into #{} ['normal-pdf 'uniform-continuous-pdf 'beta-pdf 'bernoulli-pdf 'discrete-pdf]))

(defn var-check [v rho prims]
  (and (not (contains? prims v)) (not (contains? rho v)) (not (number? v)) (not (contains? pdfs v))
  (not (coll? v))))

(defn free-vars [exp rho prims]
  (let [results (atom #{})]
         (clojure.walk/postwalk
            #(do (when (var-check % rho prims) (swap! results conj %)) %)
            exp)
        (set @results)))


(defn quoting [exp rho prims]
  (let [results (atom #{})]
         (clojure.walk/postwalk
            #(do (when (var-check % rho prims) (swap! results conj %)) %)
            exp)
        (set @results)))

(defn EVAL [exp]
  (if (and (coll? exp) (not (empty? exp)))
    (cond
       (= (first exp) 'last)
        (last (second exp))
       (= (first exp) 'vector)
        (into [] (rest exp))
       (= (first exp) 'append)
        (conj (second exp) (nth exp 2))
       (= (first exp) 'get)
       (try
         (eval exp)
       (catch Exception e
         exp))
      :else
        exp)
  exp)
  )


(defn foppl-compiler
  [rho phi exp prims]
  (if (coll? exp)
    (cond
      (vector? exp)
        (if (empty? exp)
          (let [graph (graph/new-graph)]
          (graph/add-expression graph 'vector))
          (foppl-compiler rho phi (conj (seq exp) 'vector) prims))
      (= (first exp) 'let)
        (let [v (first (second exp))
              e1 (second (second exp))
              e2 (nth exp 2)
              graph1 (foppl-compiler rho phi e1 prims)
              e2-repl (postwalk-replace {v (graph1 :E)} e2)
              graph2 (foppl-compiler rho phi e2-repl prims)
              graph (graph/merge-graphs graph1 graph2)]
              (graph/add-expression graph (EVAL (graph2 :E))))
      (= (first exp) 'if)
        (let [graph-list [(foppl-compiler rho phi (nth exp 1) prims)
                          (foppl-compiler rho phi (nth exp 2) prims)
                          (foppl-compiler rho phi (nth exp 3) prims)]
              graph (reduce graph/merge-graphs graph-list)]
        (graph/add-expression graph (EVAL (conj
                            (map graph/get-expression graph-list) (first exp)))))
      (= (first exp) 'sample)
        (let [graph-exp (foppl-compiler rho phi (second exp) prims)
              v (gensym "v")
              Z (free-vars (graph-exp :E) rho prims)
              F (score (graph-exp :E) v)
              graph (graph/new-graph)
              graph (reduce graph/add-vertex graph (conj (graph-exp :V) v))
              new-edges (into #{} (for [x Z] [x v]))
              graph (reduce graph/add-edge graph
                                  (clojure.set/union (graph-exp :A) new-edges))
              graph (reduce graph/add-prob graph
                          (clojure.set/union (graph-exp :P) (into #{} [[v  F]])))
              graph (update graph :Y (EVAL (graph-exp :Y)))]
              (graph/add-expression graph v))
      (= (first exp) 'observe)
        (let [graph1 (foppl-compiler rho phi (second exp) prims)
              graph2 (foppl-compiler rho phi (nth exp 2) prims)
              merged (graph/merge-graphs graph1 graph2)
              v (gensym "v")
              F1 (score (graph1 :E) v)
              F (list 'if phi F1 1)
              Z (disj (free-vars F1 rho prims) v)
              B (into #{} (for [x Z] [x v]))
              graph (graph/new-graph)
              graph (reduce graph/add-vertex graph (conj (merged :V) v))
              graph (reduce graph/add-edge graph
                                  (clojure.set/union (merged :A) B))
              graph (reduce graph/add-prob graph
                          (clojure.set/union (merged :P) (into #{} [[v F]])))
              graph (reduce graph/add-observed graph
                          (clojure.set/union (merged :Y) (into #{} [[v (graph2 :E)]])))]
            (graph/add-expression graph (EVAL (graph2 :E))))
      (contains? rho (first exp))
        (let [graph-list (for [e (rest exp)]
                          (foppl-compiler rho phi e prims))
              func-name (first exp)
              body ((rho func-name) :exp)
              vars ((rho func-name) :vars)
              new-exp (subst-func body vars (graph/get-expressions graph-list))
              func-graph (foppl-compiler rho phi new-exp prims)
              final-graph (reduce graph/merge-graphs (conj graph-list func-graph))]
          (graph/add-expression final-graph (func-graph :E)))
      (contains? prims (first exp))
        (let [graph-list
             (for [e (rest exp)]
             (foppl-compiler rho phi e prims))
             graph (reduce graph/merge-graphs graph-list)
             new-exp (conj (map graph/get-expression graph-list) (first exp))
             eval-exp (EVAL new-exp)]
             (graph/add-expression graph eval-exp))
      :else
        nil)
    (let [graph (graph/new-graph)
          graph (graph/add-expression graph (EVAL exp))]
          graph)))



(defn dummy [x]
  (if (coll? x)
    (if-not (empty? x)
    (cond
      (= 'let (first x))
        (d/desugar-let x)
      (= 'foreach (first x))
        ( d/desugar-foreach x)
      (= 'loop (first x))
        ( d/desugar-loop x)
      :else
        x)x)x))

(defn main-compiler [exp phi]
  (let [desugared  (postwalk dummy (postwalk dummy exp))
        extracted-exp (exp-extract desugared)
        prim p/*primitive-procedures*
        r (rho desugared)
        res (foppl-compiler r phi extracted-exp prim)
        e (pprint res)]
        [(count (res :V)) (count (res :A))]))


(def program1
  '((defn add-num [v1 v2] (+ v1 v2))
    (defn mult-num [v1 v2] (* v1 v2))
    (defn dev-num [v1 v2] (/ v1 v2))
    (add-num (mult-num fgrtg 5)(mult-num 4 (dev-num frgsww 5)))))

(def bullshit '(let [x (sample (normal 0 1))]
  (sample (normal x 1))))

(def program2
  '(let [p (sample (beta 1 1))
         x (sample (beta (exp p) 1))
         d (bernoulli (* x p))]
    (observe d 1)
    (+ p p)))


(def program3
  '(let [mu (sample (normal 1 (sqrt 5)))
           sigma (sqrt 2)
           lik (normal mu sigma)]
       (observe lik 8)
       (observe lik 9)
       mu)
)


(def program4
  '((defn observe-data [_ data slope bias]
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



(def program5
 '((defn hmm-step [t states data trans-dists likes]
      (let [z (sample (get trans-dists
                           (last states)))]
        (observe (get likes z)
                 (get data t))
        (append states z)))
(let [data [0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1
            0.0 0.13 0.45 6 0.2 0.3 -1 -1]
      trans-dists [(discrete [0.10 0.50 0.40])
                   (discrete [0.20 0.20 0.60])
                   (discrete [0.15 0.15 0.70])]
      likes [(normal -1.0 1.0)
             (normal 1.0 1.0)
             (normal 0.0 1.0)]
      states [(sample (discrete [0.33 0.33 0.34]))]]
  (loop 16 states hmm-step data trans-dists likes)))
)


(def program6
  '(let [weight-prior (normal 0 1)
      W_0 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      W_1 (foreach 10 []
            (foreach 10 [] (sample weight-prior)))
      W_2 (foreach 1 []
            (foreach 10 [] (sample weight-prior)))

      b_0 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      b_1 (foreach 10 []
            (foreach 1 [] (sample weight-prior)))
      b_2 (foreach 1 []
            (foreach 1 [] (sample weight-prior)))

      x   (mat-transpose [[1] [2] [3] [4] [5]])
      y   [[1] [4] [9] [16] [25]]
      h_0 (mat-tanh (mat-add (mat-mul W_0 x)
                             (mat-repmat b_0 1 5)))
      h_1 (mat-tanh (mat-add (mat-mul W_1 h_0)
                             (mat-repmat b_1 1 5)))
      mu  (mat-transpose
            (mat-tanh (mat-add (mat-mul W_2 h_1)
                               (mat-repmat b_2 1 5))))]
(foreach 5 [y_r y
            mu_r mu]
   (foreach 1 [y_rc y_r
               mu_rc mu_r]
      (observe (normal mu_rc 1) y_rc)))
[W_0 b_0 W_1 b_1]))


(def program7 '(let [data (vector 1 2 (sample (normal 1 1)))
      a (conj [] (sample (normal 0 2)))
      b (conj a (sample (normal 0 3)))]
  (observe (normal (second b) 4) (first (rest data)))
  b))

(main-compiler program3 'phi)
(main-compiler program4 'phi)
(main-compiler program5 'phi)
(main-compiler program6 'phi)
