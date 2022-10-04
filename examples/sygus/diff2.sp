(set-logic LIA)

(define-var x1 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var y1 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o1 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var x2 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var y2 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))
(define-var o2 Int 
    ((Start Int))
    ((Start Int ((Constant Int)))))

(define-fun diff ((x1 Int) (x2 Int)) Int (ite (<= x2 x1) (- x1 x2) (- x2 x1)))

(generator 
    ((B Bool) (AP Bool) (I Int))

    ((B Bool (true AP (or AP AP) (or AP AP AP)))
     (AP Bool ((= I I) (distinct I I)))
     (I Int (0 x1 y1 o1 x2 y2 o2)))
)

(constraint (= o1 (diff x1 y1)))
(constraint (= o2 (diff x2 y2)))
