(target-fun array_search_3 
    ((x1 Int) (x2 Int) (x3 Int) (k Int))     
    (o Int)                         
    (ite (< k x1) 0 
    (ite (< k x2) 1 
    (ite (< k x3) 2 3))) 
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (S Int) (I Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP) ($or_4 AP AP AP AP))
     (($eq_I I I) ($le_I I I) ($ge_I I I) ($lt_I I I) ($gt_I I I) ($neq_I I I)
      ($eq_S S S) ($le_S S S) ($ge_S S S) ($lt_S S S) ($gt_S S S) ($neq_S S S))
     (($zero) ($one) ($two) ($three) ($o))
     (($x1) ($x2) ($x3) ($k)))
)

;; Semantic rules
(declare-semantics 
    (B ($t) true)
    (B ($or_1 apt1) apt1)
    (B ($or_2 apt1 apt2) (or apt1 apt2))
    (B ($or_3 apt1 apt2 apt3) (or apt1 apt2 apt3))
    (B ($or_4 apt1 apt2 apt3 apt4) (or apt1 apt2 apt3 apt4))

    (AP ($eq_I it1 it2) (= it1 it2))
    (AP ($le_I it1 it2) (<= it1 it2))
    (AP ($ge_I it1 it2) (>= it1 it2))
    (AP ($lt_I it1 it2) (< it1 it2))
    (AP ($gt_I it1 it2) (> it1 it2))
    (AP ($neq_I it1 it2) (distinct it1 it2))
    (AP ($eq_S it1 it2) (= it1 it2))
    (AP ($le_S it1 it2) (<= it1 it2))
    (AP ($ge_S it1 it2) (>= it1 it2))
    (AP ($lt_S it1 it2) (< it1 it2))
    (AP ($gt_S it1 it2) (> it1 it2))
    (AP ($neq_S it1 it2) (distinct it1 it2))

    (S ($zero) 0)
    (S ($one) 1)
    (S ($two) 2)
    (S ($three) 3)
    (S ($o) o)

    (I ($x1) x1)
    (I ($x2) x2)
    (I ($x3) x3)
    (I ($k) k)
)