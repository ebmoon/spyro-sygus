(target-fun max4
    ((x1 Int) (x2 Int) (x3 Int) (x4 Int))   
    (o Int)               
    (ite (<= x2 x1) 
         (ite (<= x3 x1)
              (ite (<= x4 x1) x1 x4)
              (ite (<= x4 x3) x3 x4)) 
         (ite (<= x3 x2)
              (ite (<= x4 x2) x2 x4)
              (ite (<= x4 x3) x3 x4)))
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (AP Bool) (I Int))

    ;; Syntax
    ((($t) ($or_1 AP) ($or_2 AP AP) ($or_3 AP AP AP))
     (($eq I I) ($le I I) ($ge I I) ($lt I I) ($gt I I) ($neq I I))
     (($x1) ($x2) ($x3) ($x4) ($o)))
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

    (I ($x1) x1)
    (I ($x2) x2)
    (I ($x3) x3)
    (I ($x4) x4)
    (I ($o) o)
)
    ((Start Int ((Constant Int)))))

(define-fun max4 ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int 
                 

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP) (or AP AP AP AP)))
     (AP Bool ((= I I) (<= I I) (>= I I) (> I I) (< I I) (distinct I I)))
     (I Int (x1 x2 x3 x4 o)))
)

(constraint (= o (max4 x1 x2 x3 x4)))