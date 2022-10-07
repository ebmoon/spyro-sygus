(target-fun max2 
    ((x1 Int) (x2 Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= x2 x1) x1 x2)  ;; Function term
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I Int))

    ;; Syntax
    (($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I I) ($le I I) ($ge I I) ($lt I I) ($gt I I) ($neq I I))
     ($x1 $x2 $o))

    ;; Semantics
    (($t true) )
)

(declare-semantics 

    ;; Semantics argument
    ((x1 Int) (x2 Int) (o Int))
    
    ;; Semantic rules
    ((B $t true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_2 apt1 apt2) (or apt1 apt2 apt3))

    (AP ($eq it1 it2) (= it1 it2))
    (AP ($le it1 it2) (<= it1 it2))
    (AP ($ge it1 it2) (>= it1 it2))
    (AP ($lt it1 it2) (< it1 it2))
    (AP ($gt it1 it2) (> it1 it2))
    (AP ($neq it1 it2) (distinct it1 it2))

    (I $x1 x1)
    (I $x2 x2)
    (I $o o))
)