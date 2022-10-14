(target-fun diff1
    ((x Int) (y Int)) 
    (o Int) 
    (ite (<= y x) (- x y) (- y x))
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I I I) ($le I I I) ($ge I I I) ($lt I I I) ($gt I I I) ($neq I I I))
     (($x) ($y) ($o) ($zero)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))

    (AP ($eq it1 it2 it3) (= it1 (+ it2 it3)))
    (AP ($le it1 it2 it3) (<= it1 (+ it2 it3)))
    (AP ($ge it1 it2 it3) (>= it1 (+ it2 it3)))
    (AP ($lt it1 it2 it3) (< it1 (+ it2 it3)))
    (AP ($gt it1 it2 it3) (> it1 (+ it2 it3)))
    (AP ($neq it1 it2 it3) (distinct it1 (+ it2 it3)))

    (I ($x) x)
    (I ($y) y)
    (I ($o) o)
    (I ($zero) 0)
)
