(ns foppl-compiler.core-test
  (:require [foppl-compiler.core :refer :all]
            [clojure.set :as set]
            [anglican.runtime :refer :all]
            [foppl-compiler.desugar :refer [desugar]]
            [foppl-compiler.substitute :refer [substitute]]
            [foppl-compiler.partial-evaluation :refer [partial-evaluation]]
            [foppl-compiler.symbolic-simplify :refer [symbolic-simplify]]
            [foppl-compiler.primitives :refer :all]
            [foppl-compiler.analyze :refer [analyze empty-env empty-graph]]
            [foppl-compiler.free-vars :refer [free-vars]])
            (:use [anglican core emit runtime]
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

(defn get-parents [m var]
  (let [f (filter (fn [[k v]] (contains? v var)) m)]
       [var (map first f)]
    ))

(defn get-parents-for-all [graph]
  (into (sorted-map) (map #(get-parents (graph :A) %) (graph :V)))
)

(defn subst [exp vals]
  (postwalk-replace vals exp))


(def select-values (comp vals select-keys))

(defn accept [children var X X_prime links observe-map] ;;parents is a map with parents for all variables
                                       ;;var is small x
                                       ;;X is sample variables and their previous step assignments
                                       ;;X_prime is sample variables and their new assignments
        (loop [V_x (children var)
              log_alpha 0]
              (if (empty? V_x)
               (exp log_alpha)
               (let [
                 v (first V_x)
                 fun-key (observe-map v)
                 fun (first fun-key)
                 depends (second fun-key)
                 varsX (subst depends X)
                 varsXprime (subst depends X_prime)
                 appX (apply fun varsX)
                 appXprime (apply fun varsXprime)
                 log_alpha (+ log_alpha appXprime)
                 log_alpha (- log_alpha appX)
                 ]
                 (recur (rest V_x) log_alpha))

)))

(defn gibbs-step [[children links X vars output sample-map observe-map evaled-output]]
  (lazy-seq (
  let [sample
  (loop [vars vars
         X X]
        (if (empty? vars)
          X
          (let [
            x (first vars)
            fun-key (sample-map x)
            fun (first fun-key)
            key (second fun-key)
            ss (subst key X)
            q (apply fun ss)
            X_prime  X
            X_prime (assoc X_prime x q)
            alpha (accept children x X X_prime links observe-map)
            u (sample* (uniform-continuous 0 1))]
            (if (< u alpha) (recur (rest vars) X_prime) (recur (rest vars) X)))
        )
  )
  ]
  (cons (postwalk-replace {true 1.0 false 0.0} (apply (first evaled-output) (postwalk-replace  sample (second evaled-output)))) (gibbs-step [children links sample vars output sample-map observe-map evaled-output])))
))



(defn eval-part-sample [depends key exp]
  (if (= (first exp) 'observe*)
      [(eval (conj (conj (conj () (conj (conj () (second exp)) 'sample*)) depends) 'fn)) depends]
      [(eval (conj (conj (conj () exp) depends) 'fn)) depends]))


(defn eval-part-observe [depends key exp]
  (if (= (first exp) 'sample*)
    [(eval (conj (conj (conj () (conj (conj (conj () key)  (second exp)) 'observe*)) (conj depends key)) 'fn)) (conj depends key)]
    [(eval (conj (conj (conj () exp) depends) 'fn)) depends]))

(defn make-map-sample [inv-graph links]
  (loop [links links
        result {}]
      (if (empty? links)
        result
        (let [
            key-exp (first links)
            key (first key-exp)
            exp (second key-exp)
            depends (get inv-graph key)
            depends (into [] depends)
            res (eval-part-sample depends key exp)
          ](recur (rest links) (conj result [key res]))))
      )
  )

(defn make-map-observe [inv-graph links]
  (loop [links links
        result {}]
      (if (empty? links)
        result
        (let [
            key-exp (first links)
            key (first key-exp)
            exp (second key-exp)
            depends (get inv-graph key)
            depends (into [] depends)
            res (eval-part-observe depends key exp)
          ](recur (rest links) (conj result [key res]))))
      )
  )

(defn make-map-return [exp]
  (let [fv (into [] (free-vars exp *bound*))]
      [(eval (list 'fn fv exp)) fv])
  )

(defn gibbs-prep [program]
  (let [graph (program->graph (evaled-desugared program))
        output (last graph)
        instr (graph->instructions graph)
        eval-instr (eval-instructions instr)
        graph (second graph)
        children (graph :A)
        links (graph :P)
        X (into {} (drop-last eval-instr))
        vars (keys (graph :A))
        inv-graph (invert-graph (:A graph))
        sample-map (make-map-sample inv-graph links)
        observe-map (make-map-observe inv-graph links)
        return-map (make-map-return output)
        ]
        [children links X vars output sample-map observe-map return-map]
    ))

(gibbs-prep program1)

(take 100 (gibbs program1))


(defn gibbs [program]
    (let [params (gibbs-prep program)]
          (gibbs-step params)))


(def program1 '((let [mu (sample (normal 1 (sqrt 5)))
           sigma (sqrt 2)
           lik (normal mu sigma)]
       (observe lik 8)
       (observe lik 9)
       mu)))


(def program2
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


(def program4 '((let [sprinkler true
      wet-grass true
      is-cloudy (sample (flip 0.5))

      is-raining (if (= is-cloudy true )
                    (sample (flip 0.8))
                    (sample (flip 0.2)))
      sprinkler-dist (if (= is-cloudy true)
                        (flip 0.1)
                        (flip 0.5))
      wet-grass-dist (if (and (= sprinkler true)
                              (= is-raining true))
                        (flip 0.99)
                        (if (and (= sprinkler false)
                                 (= is-raining false))
                          (flip 0.0)
                          (if (or (= sprinkler true)
                                  (= is-raining true))
                            (flip 0.9))))]
  (observe sprinkler-dist sprinkler)
  (observe wet-grass-dist wet-grass)
  is-raining)))

(def program3 '((let [data [1.1 2.1 2.0 1.9 0.0 -0.1 -0.05]
                                                    likes (foreach 3 []
                                                                   (let [mu (sample (normal 0.0 10.0))
                                                                         sigma (sample (gamma 1.0 1.0))]
                                                                     (normal mu sigma)))
                                                    pi (sample (dirichlet [1.0 1.0 1.0]))
                                                    z-prior (discrete pi)
                                                    z (foreach 7 [y data]
                                                               (let [z (sample z-prior)]
                                                                 (observe (get likes z) y)
                                                                 z))]
                                                (= (first z) (second z)))))




(let [samples (take 100000 (drop 10000(gibbs program1)))]
        (mean samples) )
(let [samples (take 200000 (drop 10000 (gibbs program2)))]
        (mean samples))
(let [samples (take 100000 (drop 10000 (gibbs program3)))]
        (mean samples) )
(let [samples (take 10000 (drop 10000 (gibbs program4)))]
          (mean samples))





(gibbs-prep program3)

(let [  anglican (->>
                  (doquery :smc
                           (query []
                                  (let [mu (sample (normal 1 (sqrt 5)))
                                        sigma (sqrt 2)
                                        lik (normal mu sigma)]
                                    (observe lik 8)
                                    (observe lik 9)
                                    mu))
                           []
                           :number-of-particles 10000)
                  (drop 10000)
                  (map :result)
                  (take 100000))]
    [(mean anglican) (std anglican)])

(let [
  anglican (->>
    (doquery :smc (query []
                                (let [data [1.1 2.1 2.0 1.9 0.0 -0.1 -0.05]
                                      likes (map (fn [_] (let [mu (sample (normal 0.0 10.0))
                                                               sigma (sample (gamma 1.0 1.0))]
                                                           (normal mu sigma)))
                                                 (range 3))
                                      pi (sample (dirichlet [1.0 1.0 1.0]))
                                      z-prior (discrete pi)

                                      z (map (fn [y]
                                               (let [z (sample z-prior)]
                                                 (observe (nth likes z) y)
                                                 z))
                                             data)]
                                  (= (first z) (second z))))
                    []
                    :number-of-particles 10000)
           (drop 20000)
           (map :result)
           (take 100000)
           (map #(if % 1.0 0.0)))]
            (mean anglican))


(let [
  anglican (->>
             (doquery :smc (query []
                                  (let [sprinkler true
                                        wet-grass true
                                        is-cloudy (sample (flip 0.5))

                                        is-raining (if (= is-cloudy true )
                                                     (sample (flip 0.8))
                                                     (sample (flip 0.2)))
                                        sprinkler-dist (if (= is-cloudy true)
                                                         (flip 0.1)
                                                         (flip 0.5))
                                        wet-grass-dist (if (and (= sprinkler true)
                                                                (= is-raining true))
                                                         (flip 0.99)
                                                         (if (and (= sprinkler false)
                                                                  (= is-raining false))
                                                           (flip 0.0)
                                                           (if (or (= sprinkler true)
                                                                   (= is-raining true))
                                                             (flip 0.9))))]
                                    (observe sprinkler-dist sprinkler)
                                    (observe wet-grass-dist wet-grass)
                                    is-raining))
                      []
                      :number-of-particles 10000)
             (drop 10000)
             (map :result)
             (take 10000)
             (map #(if % 1.0 0.0)))]

            (mean anglican))



(let [
      anglican (->>
                (doquery :smc (let [observe-data
                                    (fm [xn yn slope bias]
                                        (let [zn (+ (* slope xn) bias)]
                                          (observe (normal zn 1.0) yn)))]

                                (query []
                                       (let [slope (sample (normal 0.0 10.0))
                                             bias  (sample (normal 0.0 10.0))
                                             data (vector 1.0 2.1 2.0 3.9 3.0 5.3
                                                          4.0 7.7 5.0 10.2 6.0 12.9)
                                             xn (take-nth 2 data)
                                             yn (take-nth 2 (rest data))]
                                         (loop [i 0]
                                           (when (< i 6)
                                             (observe-data (nth xn i) (nth yn i) slope bias)
                                             (recur (inc i))))
                                         (vector slope bias))))
                         []
                         :number-of-particles 10000)
                (drop 10000)
                (map :result)
                (take 200000))]
  [(mean (map first anglican))(mean (map second anglican))(std (map first anglican)) (std (map second anglican))])
