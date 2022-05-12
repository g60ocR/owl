
(define seed (time-ms))

(define (test n max)
   (lets
      ((rs (seed->rands seed))
       (rs nums (random-numbers rs max n))
       (vec (list->vector nums)))
      (print (list (if (equal? (vector->list vec) nums) 'ok 'fail) 'n n 'max max))))


(for-each
   (λ (n) (for-each (H test n) (list 1 255 260 100000000000)))
   (list 1 10 100 1000 10000))

;(test ;; vec-iter-range = read values separately
;   (lmap
;      (λ (rst)
;         (lets
;            ((rst n (rand rst 10000))
;             (vec (list->vector (random-numbers rst n n)))
;             (rst end (rand rst n))
;             (rest start (rand rst end)))
;            (tuple vec start end)))
;      (liter rand-succ (lets ((ss ms (clock))) (+ (* ss 1000) ms))))
;   (λ (t) (lets ((v s e t)) (force (vec-iter-range v s e))))
;   (λ (t) (lets ((v s e t)) (map (H vector-ref v) (iota s 1 e)))))
;(test ;; vector fold[r]
;   (lmap
;      (λ (rst)
;         (lets
;            ((rst n (rand rst 10000))
;             (vec (list->vector (random-numbers rst n n))))
;            vec))
;      (liter rand-succ (lets ((ss ms (clock))) (+ (* ss 1000) ms))))
;   (λ (v) (vec-foldr cons #n v))
;   (λ (v) (reverse (vec-fold (λ (a b) (cons b a)) #n v))))
