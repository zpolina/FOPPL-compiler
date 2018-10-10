(ns foppl-compiler.autodiff
  (:use [anglican core emit runtime]
                [foppl-compiler.primitives :as p]
                [clojure.walk]
                  [clojure.pprint]))


(def partial-fns
    (reduce
      merge
      (list
        {'* [(fn [a b] b) (fn [a b] a)]}
        ; f(a,b) = a * b <-> (* a b)
        ; df/da = b
        ; df/db = a

        {'- [(fn [a b] 1) (fn [a b] -1)]}
        ; f(a,b) = a - b <-> (- a b)
        ; df/da = 1
        ; df/db = -1

        {'+ [(fn [a b] 1) (fn [a b] 1)]}
        ; f(a,b) = a + b <-> (+ a b)
        ; df/da = 1
        ; df/db = 1

        {'/ [(fn [a b] (/ 1 b)) (fn [a b] (* a (/ -1 (* b b))))]}
        ; f(a,b) = a / b <-> (/ a b)
        ; df/da = 1
        ; df/db = -1/b^2

        {'exp [(fn [a] (exp a))]}
        ; f(a) = (exp a)
        ; df/da = (exp a)

        {'relu [(fn [a] (if (> a 0) 1 0))]}
        ; f(a) = (relu a)
        ; df/da = 1 if a > 0, 0 otherwise

        {'log [(fn [a] (/ 1 a))]}

        {'normpdf [(fn [a b c] (/ (- b a) (* c c))) (fn [a b c] (/ (- a b) (* c c)))
                    (fn [a b c] (- (/ (* (- a b) (- a b)) (* c (* c c))) (/ 1 c)))]}

        {'sin [(fn [a] (cos a))]})))


(defn normpdf [y m s]
  (observe* (normal m s) y))



(def graph
  {:V {}  ;;vertices and their forward mode values
   :Child_Nodes {}  ;;children in a backward mode
   :Parent_Nodes {}  ;;parents in a backward more
   :vars_exps {} ;;maping from variables to expressions
  })

(defn add-vertex [graph [v value]]
 (update graph :V conj [v value]))

(defn add-CN [graph [v parent]]
  (if (contains? (graph :Child_Nodes) v)
  (update-in graph [:Child_Nodes v] conj parent)
  (update graph :Child_Nodes conj [v [parent]])))

(defn add-PN [graph [v parent]]
  (if (contains? (graph :Parent_Nodes) v)
  (update-in graph [:Parent_Nodes v] conj parent)
  (update graph :Parent_Nodes conj [v [parent]])))

(defn add-vars_exps [graph [v exp]]
    (update graph :vars_exps conj [v exp]))



(defn graph-build [child exp graph prims]
  (if (coll? exp)
    (cond
      (= (first exp) 'if)
        (let [pure-exp (postwalk-replace (graph :V) (second exp))
              r (println pure-exp)
              eval-exp (eval pure-exp)
              exp (if eval-exp
                (nth exp 2)
                (nth exp 3))]
          (graph-build child exp graph prims)
        )
      (or (contains? prims (first exp)) (= 'normpdf (first exp)))
      (let [var (gensym "v")
            graph (add-CN graph [var child])
            graph (add-PN graph [child var])
            graph (add-vars_exps graph [var (first exp)])]
        (cond
          (= (count (rest exp)) 1)
            (let [
              rec (graph-build var (second exp) graph prims)
              graph (first rec)
              value (second rec)
              new_val (eval (sequence [(first exp) value]))
              graph (add-vertex graph [var new_val])
            ] [graph new_val])
          (= (count (rest exp)) 2)
            (let [
              rec (graph-build var (second exp) graph prims)
              graph (first rec)
              value1 (second rec)
              rec (graph-build var (nth exp 2) graph prims)
              graph (first rec)
              value2 (second rec)
              new_val (eval (sequence [(first exp) value1 value2]))
              graph (add-vertex graph [var new_val])
            ] [graph new_val])
          (= (count (rest exp)) 3)
            (let [
              rec (graph-build var (second exp) graph prims)
              graph (first rec)
              value1 (second rec)
              rec (graph-build var (nth exp 2) graph prims)
              graph (first rec)
              value2 (second rec)
              rec (graph-build var (nth exp 3) graph prims)
              graph (first rec)
              value3 (second rec)
              new_val (eval (sequence [(first exp) value1 value2 value3]))
              graph (add-vertex graph [var new_val])
            ] [graph new_val])
          ))
      :else
        nil
      )
    (if (number? exp)
    (let [graph (add-PN graph [child exp])]
      [graph exp])
      (let [graph (add-CN graph [exp child])
            graph (add-PN graph [child exp])]
        [graph ((graph :V) exp)]))
    ))


(defn propagation [graph node der res] ;; graph,
  ;;
  ;;value of derivitive from the previous step,
  ;;resulting map with derivitives, if already has a value then add it up
  (if (contains? (graph :Parent_Nodes) node)
  (let [vars ((graph :Parent_Nodes) node)
        eval-vars (postwalk-replace (graph :V) vars)
        op ((graph :vars_exps) node)
        new_der (apply (apply juxt (partial-fns op)) eval-vars)
        new_der (map #(* % der) new_der)]
        (cond
          (= (count new_der) 1)
            (propagation graph (first vars) (first new_der) res)
          (= (count new_der) 2)
            (let [res (propagation graph (first vars) (first new_der) res)]
                (propagation graph (second vars) (second new_der) res))
          (= (count new_der) 3)
          (let [res (propagation graph (first vars) (first new_der) res)
                res (propagation graph (second vars) (second new_der) res)]
              (propagation graph (nth vars 2) (nth new_der 2) res))
        )
  )
  (if (contains? res node)
      (update res node + der)
      res
  )
)
)


(defn autodiff [func arg-vals]
    (let [[op args body] func
          gr (graph-build 'f body {:V (zipmap args arg-vals) :Child_Nodes {}
                                  :Parent_Nodes {} :vars_exps {}} p/*primitive-procedures*)
          r (println gr)
          val (second gr)
          gr (first gr)
          mapping (propagation gr (first ((gr :Parent_Nodes) 'f)) 1.0 (zipmap args (vec (replicate (count args) 0.0))))
         ]
        [val mapping]
      )
  )


(def program1
  '(fn [x] (exp (sin x))))
(autodiff program1 [0])

(def program2
  '(fn [x y] (+ (* x x) (sin x))))
(autodiff program2 [0 10])

(def program3
  '(fn [x] (if (> x 5) (* x x) (+ x 18))))
(autodiff program3 [5.000001])

(def program4
  '(fn [x] (log x)))
(autodiff program4 [0.1])


(def program5
  '(fn [x mu sigma] (+ (- 0 (/ (* (- x mu) (- x mu))
                    (* 2 (* sigma sigma))))
                    (* (- 0 (/ 1 2)) (log (* 2 (* 3.141592653589793 (* sigma sigma))))))))
(autodiff program5 [10 0 2])


(def program6
  '(fn [x mu sigma] (normpdf x mu sigma)))
(autodiff program6 [10 0 2])


(def program7
  '(fn [x1 x2 x3] (+ (+ (normpdf x1 2 5)
                        (if (> x2 7)
                          (normpdf x2 0 1)
                          (normpdf x2 10 1)))
                    (normpdf x3 -4 10))))
(autodiff program7 [2 7.01 5])


(defn addd [exprl i d]
  (if (= i 0)
    (reduce conj [`(~'+ ~d ~(first exprl))] (subvec exprl 1))
    (reduce conj (subvec exprl 0 i)
            (reduce conj [`(~'+ ~d ~(get exprl i))] (subvec exprl (+ i 1))))))

(defn finite-difference-expr [expr args i d]
  `(~'/ (~'- (~expr ~@(addd args i d)) (~expr ~@args)) ~d))

(defn finite-difference-grad [expr]
  (let [[op args body] expr
        d (gensym)
        fdes (map #(finite-difference-expr expr args % d) (range (count args)))
        argsyms (map (fn [x] `(~'quote ~x)) args)]
    `(~'fn [~@args]
       (~'let [~d 0.001]
         ~(zipmap argsyms fdes)))))


((eval (finite-difference-grad program7)) 2 7.01 5)
