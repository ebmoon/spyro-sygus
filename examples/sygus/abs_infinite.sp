(set-logic LIA)

(define-var x Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun abs ((x Int)) Int (ite (>= x 0) x (- x)))

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP)))
     (AP Bool ((= I (+ I I)) (<= I (+ I I)) (>= I (+ I I)) 
               (> I (+ I I)) (< I (+ I I)) (distinct I (+ I I))))
     (I Int ((Constant Int) x o)))
)

(constraint (= o (abs x)))
