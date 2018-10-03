(ns foppl-compiler.graph
  (:use [anglican core emit runtime]))


 (def graph
   {:V (set nil)
    :A (set nil)
    :P {}
    :Y {}
    :E nil})

(defn new-graph []
  graph)

(defn add-vertex [graph v]
  (update graph :V clojure.set/union #{v}))

(defn add-edge [graph [v1 v2]]
  (update graph :A clojure.set/union #{(list v1 v2)}))

(defn add-prob [graph [v prob]]
  (update graph :P conj [v prob]))

(defn add-observed [graph [v val]]
  (update graph :Y conj [v val]))

(defn add-expression [graph exp]
  (assoc graph :E exp))

(defn merge-graphs [graph1 graph2]
  (let [graph (new-graph)
        graph (reduce add-vertex graph (clojure.set/union (graph1 :V) (graph2 :V)))
        graph (reduce add-edge graph (clojure.set/union (graph1 :A) (graph2 :A)))
        graph (reduce add-prob graph (merge (graph1 :P) (graph2 :P)))
        graph (reduce add-observed graph (merge (graph1 :Y) (graph2 :Y)))]
        graph))

(defn get-expression [graph]
  (graph :E))

(defn get-expressions [graphs]
 (map get-expression graphs))
