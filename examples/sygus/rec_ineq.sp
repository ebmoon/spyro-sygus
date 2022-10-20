(target-fun f 
    ((x Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= 0 x) (+ (f (- x 1)) 1) 0)  ;; Function term
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (I Int))

    ;; Syntax
    ((($o_gt I))
     (($n Int)))
)

;; Semantic rules
(declare-semantics 
    (B ($o_gt it) (>= o it))

    (I ($n num) num)
)
