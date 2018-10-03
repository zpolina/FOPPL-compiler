(ns foppl-compiler.desugar
  (:use [anglican core emit runtime]))

(use 'clojure.walk)

(def sugared-let
  '(defn [v2] (let [] 2)))

(defn partial-desugar-let
  [dec exp]
    (cond
      (empty? dec)
        (cond
          (empty? exp)
            exp
          (= 1 (count exp))
           (first exp)
          :else
          (read-string (apply str "(let ["  (gensym "x") " " (first exp) "]"
          (partial-desugar-let [] (into [] (rest exp))) ")"))
        )
      (vector? dec)
        (read-string (apply str "(let [" (first dec) " " (second dec) "]"
        (partial-desugar-let (into [] (nthrest dec 2)) exp) ")"))
      :else dec)

)
(defn desugar-let
  [v]
  (if (and (seq? v) (= 'let (first v)))
      (let [dec (second v)
            exp (into [] (nthrest v 2))]
            (partial-desugar-let dec exp))
      v))

(postwalk desugar-let sugared-let)

(def sugared-foreach
  '(defn abc [v2] (foreach 4 [] (+ v1 v2) (* v1 v2))))

(defn partial-desugar-foreach
  [vars_exps num]
   (loop  [vars_exps vars_exps
           num num
           result []]
           (if (empty? vars_exps)
             result
             (recur (nthrest vars_exps 2) num
                    (conj result (symbol (apply str (first vars_exps) " "
                                  "(get " (second vars_exps) " "  num")")))))))

(defn desugar-foreach
  [exp]
  (if (and (seq? exp) (= 'foreach (first exp)))
    (let [new_exp
      (for [c (range 0 (second exp))]
      (conj (conj (nthrest exp 3) (partial-desugar-foreach (nth exp 2) c)) 'let))]
      ;;(partial-desugar-let (partial-desugar-foreach (nth exp 2) c) (nthrest exp 3)))]
      (conj new_exp 'vector)
      )
    exp))


(postwalk desugar-foreach sugared-foreach)


(def sugared-loop
  '(defn fff [v1 v2](loop 5 0.0 (* (* x1 x2) (+ x3 x4)) v1 v2)))

(defn generator_as
  [size]
  (loop [x size
         result []]
    (if (> x 0)
    (recur (- x 1)
          (conj result (gensym "a")))
    result)))

(defn partial-desugar-loop
  [exps as]
  (into [] (for [i (range (count exps))]
        (symbol (str (nth as i) " " (nth exps i))))))

(defn recr-desugar-loop
  [f next_num c e as]
     (if (= next_num c)
          e
          (let [sym (gensym "v")
                bind (conj (conj (conj () e) next_num) f)
                line (concat bind as)]
                (read-string (apply str "(let ["  sym " (" (clojure.string/join " " line) ")]"
                (recr-desugar-loop f (+ 1 next_num) c sym as) ")")))))

(defn desugar-loop
  [exp]
    (if (and (seq? exp) (= 'loop (first exp)))
    (let [c (second exp)
          e (nth exp 2)
          f (nth exp 3)
          exps (nthrest exp 4)
          as (generator_as (count exps))]
          (conj (conj (conj () (recr-desugar-loop f 0 c e as)) (partial-desugar-loop exps as)) 'let))
    exp))

(postwalk desugar-loop sugared-loop)
