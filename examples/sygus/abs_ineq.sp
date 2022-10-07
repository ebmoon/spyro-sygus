(set-logic LIA)

(define-var x Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun abs ((x Int)) Int (ite (>= x 0) x (- x)))

(generator 
    ((B Bool) (N Int))

    ((B Bool ((>= o N)))
     (N Int ((Constant Int))))
)

(constraint (= o (abs x)))
