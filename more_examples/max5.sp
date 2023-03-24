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
(define-var x5 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun max5 ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int)) Int 
                 (ite (<= x2 x1) 
                      (ite (<= x3 x1)
                           (ite (<= x4 x1)
                                (ite (<= x5 x1) x1 x5)
                                (ite (<= x5 x4) x4 x5))
                           (ite (<= x4 x3)
                                (ite (<= x5 x3) x3 x5)
                                (ite (<= x5 x4) x4 x5))) 
                      (ite (<= x3 x2)
                           (ite (<= x4 x2)
                                (ite (<= x5 x2) x2 x5)
                                (ite (<= x5 x4) x4 x5))
                           (ite (<= x4 x3)
                                (ite (<= x5 x3) x3 x5)
                                (ite (<= x5 x4) x4 x5)))))

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP) (or AP AP AP AP) (or AP AP AP AP AP)))
     (AP Bool ((= I I) (<= I I) (>= I I) (> I I) (< I I) (distinct I I)))
     (I Int (x1 x2 x3 o)))
)

(constraint (= o (max5 x1 x2 x3 x4 x5)))