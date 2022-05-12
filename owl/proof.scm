#| doc
Automatic Tests & Documentation

The goal of this library is to make writing software tests and documenting functionality 
as simple as possible. The operation is as follows:
 - Tests run automatically when a program or library is loaded. Failure aborts the load via an error.
 - Tests can be collected from code automatically for documentation.
 - To add tests, import (owl proof) and write an example.
 
    > (import (owl proof))
    > (example
         (+ 1 2) = (+ 2 1)
         (car (cons 1 2)) = 1)
|#
(define-library (owl proof)

   (export
      theorem
      theorem-equal?
      example)

   (import
      (owl core)
      (only (owl syscall) error)
      (owl equal-prim))

   (begin

      ;; operation tries to avoid external library dependencies to allow
      ;; testing of as many libraries as possible

      (define (luncons ll)
         (if (eq? type-pair (type ll))
            (values (car ll) (cdr ll))
            (luncons (ll))))

      ;; generator = #(label generator acceptor)
      ;; (generator RS) -> RS' value

      (define (generate-literal val)
         (λ (rs) (values rs val)))

      ;; options are generators
      '(define generate-any
         (λ options
            (let ((n (length options)))
               (cond
                  ((eq? n 0)
                     (error "no options given for Any"))
                  ((eq? 0 (type n))
                     ;; we don't want to depend on bignum math internally
                     (error "Any has too many options"))
                  (else
                     (λ (rs)
                        (let ((rs f (luncons rs)))
                           ((list-ref options (bound-fixnum f n))
                              rs))))))))

      ;; (theorem
      ;;   ((ℕ a b)
      ;;    (List l))
      ;;   (equal?
      ;;      (cons a l)
      ;;      (cons b l)))

      (define-syntax theorem-body
         (syntax-rules (≡)
            ((theorem-body rs env A ≡ B)
               (if (equal? A B)
                  (values rs #false)
                  (values rs (tuple 'mismatch (quote A) (quote B) env))))))

      (define-syntax theorem-decls
         (syntax-rules ()
            ((theorem-decls rs env () . body)
               (theorem-body rs env . body))
            ((theorem-decls rs env ((type n . ns) . rest) . body)
               (lets ((rs n (generate rs type)))
                  (theorem-decls rs
                     (put env 'n n)
                     ((type . ns) . rest) . body)))))

      (define-syntax theorem
         (syntax-rules ()
            ((theorem decls . body)
               (λ (rs)
                  (theorem-decls rs empty decls . body)))))

      (define theorem-equal? simple-equal?)

      ;; equal has to be defined in the context where example is used
      (define-syntax example
         (syntax-rules (theorem-equal? = receive let)
            ((example let a = b . rest)
               (let ((a b))
                  (example . rest)))
            ((example term-a = term-b . rest)
               (let ((eva (λ () term-a))
                     (evb (λ () term-b)))
                  (receive (eva)
                     (λ as
                        (receive (evb)
                           (λ bs
                              (if (not (theorem-equal? as bs))
                                 (error "example does not hold: " (list (quote term-a) " evalutes to values " as))
                                 (example . rest))))))))
            ((example)
               #true)))

      (example 1 = 1)

      (example (cons 1 2) = '(1 . 2))

      (example (values 1 2) = (values 1 2))
))












