(target-fun diff1
    ((x1 Int) (y1 Int)) 
    (o1 Int) 
    (ite (<= y1 x1) (- x1 y1) (- y1 x1))
)
(target-fun diff2
    ((x2 Int) (y2 Int)) 
    (o2 Int) 
    (ite (<= y2 x2) (- x2 y2) (- y2 x2))
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I1 Int) (I2 Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I1 I2) ($neq I1 I2))
     (($x1) ($y1) ($o1)) 
     (($x2) ($y2) ($o2)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (AP ($eq it1 it2) (= it1 it2))
    (AP ($neq it1 it2) (distinct it1 it2))

    (I1 ($x1) x1)
    (I1 ($y1) y1)
    (I1 ($o1) o1)
    
    (I2 ($x2) x2)
    (I2 ($y2) y2)
    (I2 ($o2) o2)
)
