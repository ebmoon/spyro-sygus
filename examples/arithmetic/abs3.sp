(target-fun abs
    ((x Int))     ;; Input variables
    (o Int)                 ;; Output variable
    (ite (<= 0 x) x (- x))  ;; Function term
)

(declare-language
    
    ;; Nonterminals
    ((B Bool) (I Int))

    ;; Syntax
    ((($o_gt I))
     (($zero) ($succ I)))
)

;; Semantic rules
(declare-semantics 
    (B ($o_gt it) (or (> x 10) (< x (- 20)) (<= o it)))

    (I ($zero) 0)
    (I ($succ it) (+ it 1))
)
