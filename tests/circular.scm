(define-library (tests circular)
   (import
      (owl core)
      (tests circular))
   (export bad-kitty)
   (begin
      (define bad-kitty
         (map (λ (x) 'paw) (iota 0 1 4)))))
