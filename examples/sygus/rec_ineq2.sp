(target-fun f 
    ((x Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= 0 x) (+ (f (- x 1)) x) 0)  ;; Function term
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (HEAD Bool) (BODY Bool) (I Int) (N Int))

    ;; Syntax
    ((($t) ($or_1 BODY) ($or_2 BODY HEAD) ($or_3 BODY BODY HEAD))
     (($o_eq I I) ($o_ge I N))
     (($eq I I) ($le I I) ($ge I I) ($lt I I) ($gt I I) ($neq I I))
     (($x) ($zero) ($one))
     (($n Int)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (HEAD ($o_eq it1 it2) (= o (+ it1 it2)))
    (HEAD ($o_ge it1 it2) (>= o (+ it1 it2)))
    
    (BODY ($eq it1 it2) (= it1 it2))
    (BODY ($le it1 it2) (<= it1 it2))
    (BODY ($ge it1 it2) (>= it1 it2))
    (BODY ($lt it1 it2) (< it1 it2))
    (BODY ($gt it1 it2) (> it1 it2))
    (BODY ($neq it1 it2) (distinct it1 it2))

    (I ($x) x)
    (I ($zero) 0)
    (I ($one) 1)

    (N ($n num) num)
)
