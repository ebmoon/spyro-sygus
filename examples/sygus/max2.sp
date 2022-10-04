(set-logic LIA)

(define-var x1 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var x2 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun max2 ((x1 Int) (x2 Int)) Int (ite (<= x2 x1) x1 x2))

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP)))
     (AP Bool ((= I I) (<= I I) (>= I I) (> I I) (< I I) (distinct I I)))
     (I Int (x1 x2 o)))
)

(constraint (= o (max2 x1 x2)))
