(ns foppl-compiler.demo-test
  (:require [clojure.test :refer :all]
            [foppl-compiler.desugar :as d]))

(deftest add-numbers-test
  (testing "Add two numbers"
    (is (= 5 (+ 2 3)))))

(deftest subtract-numbers-test
  (testing "Subtract two numbers"
    (is (= 1 (- 3 2)))))


(def sugared-let
  '(defn [v2] (let [v1 (+ 1 2)
                    v2 (* 3 4)]
        (+ v1 v1)
        (* v1 v1)
        (* v2 v2))))


(deftest subtract-numbers-test
  (testing "Subtract two numbers"
    (is (= '(defn [v2] (let [v1 (+ 1 2) v2 (* 3 4)] (+ v1 v1) (* v1 v1) (* v2 v2)))
    (d/desugar-let sugared-let)))))





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
 (let [data (vector 0.9 0.8 0.7 0.0 -0.025 -5.0 -2.0 -0.1
             0.0 0.13 0.45 6 0.2 0.3 -1 -1)
       trans-dists [(discrete [0.10 0.50 0.40])
                    (discrete [0.20 0.20 0.60])
                    (discrete [0.15 0.15 0.70])]
       likes [(normal -1.0 1.0)
              (normal 1.0 1.0)
              (normal 0.0 1.0)]
       states [(sample (discrete [0.33 0.33 0.34]))]]
   (loop 16 states hmm-step data trans-dists likes))))


(comment
   (let [graph1 (new-graph)
         graph1 (add-edge graph1 ['v1 'v2])
         graph1 (add-vertex graph1 'v1')
         graph1 (add-prob graph1 ['v1' "normal"])
         graph1 (add-observed graph1 ['v2 '0.5])
         graph2 (new-graph)
         graph2 (add-vertex graph2 'v4')
         graph2 (add-edge graph2 ['v3 'v4])]
         (do (println (merge (graph1 :P) (graph2 :P)))
           (merge-graphs graph1 graph2)))


   (let [graph1 (new-graph)
         graph1 (add-expression graph1 '(+ 1 2))
         graph2 (new-graph)
         graph2 (add-expression graph2 '(* 1 2))
         graph3 (new-graph)
         graph3 (add-expression graph3 '(/ 1 2))
         graph4 (new-graph)
         graph4 (add-expression  graph4 '(- 1 2))]
         (get-expressions (sequence [graph1 graph2 graph3 graph4]))))
