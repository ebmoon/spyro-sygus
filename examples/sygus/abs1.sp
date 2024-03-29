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
     (($eq I I) ($le I I) ($ge I I) ($lt I I) ($gt I I) ($neq I I))
     (($x) ($minus_x) ($o) ($minus_o) ($zero)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (AP ($eq it1 it2) (= it1 it2))
    (AP ($le it1 it2) (<= it1 it2))
    (AP ($ge it1 it2) (>= it1 it2))
    (AP ($lt it1 it2) (< it1 it2))
    (AP ($gt it1 it2) (> it1 it2))
    (AP ($neq it1 it2) (distinct it1 it2))

    (I ($x) x)
    (I ($minus_x) (- x))
    (I ($o) o)
    (I ($minus_o) (- o))
    (I ($zero) 0)
)