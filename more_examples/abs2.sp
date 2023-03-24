(target-fun abs
    ((x Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= 0 x) x (- x))  ;; Function term
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I I I) ($le I I I) ($ge I I I) ($lt I I I) ($gt I I I) ($neq I I I))
     (($minus_three) ($minus_two) ($minus_one) ($zero) ($one) ($two) ($three) ($four)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (AP ($eq it1 it2 it3) (= (+ (* it1 x) (* it2 o)) it3))
    (AP ($le it1 it2 it3) (<= (+ (* it1 x) (* it2 o)) it3))
    (AP ($ge it1 it2 it3) (>= (+ (* it1 x) (* it2 o)) it3))
    (AP ($lt it1 it2 it3) (< (+ (* it1 x) (* it2 o)) it3))
    (AP ($gt it1 it2 it3) (> (+ (* it1 x) (* it2 o)) it3))
    (AP ($neq it1 it2 it3) (distinct (+ (* it1 x) (* it2 o)) it3))

    (I ($minus_three) (- 3))
    (I ($minus_two) (- 2))
    (I ($minus_one) (- 1))
    (I ($zero) 0)
    (I ($one) 1)
    (I ($two) 2)
    (I ($three) 3)
    (I ($four) 4)
)