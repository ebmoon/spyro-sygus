(set-logic LIA)

(define-var x1 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var x2 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var x3 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var x4 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun max4 ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Int 
                 (ite (<= x2 x1) 
                      (ite (<= x3 x1)
                           (ite (<= x4 x1) x1 x4)
                           (ite (<= x4 x3) x3 x4)) 
                      (ite (<= x3 x2)
                           (ite (<= x4 x2) x2 x4)
                           (ite (<= x4 x3) x3 x4))))

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP) (or AP AP AP AP)))
     (AP Bool ((= I I) (<= I I) (>= I I) (> I I) (< I I) (distinct I I)))
     (I Int (x1 x2 x3 o)))
)

(constraint (= o (max4 x1 x2 x3 x4)))