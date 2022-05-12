#| doc
Fresh Symbols

It is sometimes useful to get symbols, which do not occur elsewhere.
This is typically needed in the compiler, but it may also be needed
elsewhere. Gensyms in Owl are just regular symbols, which do not
occur in a given expression. This requires walking through the whole
expression. To avoid having to walk the original expression in many
cases when gensyms are needed, they work in a way that ensures that
the gensym of the gensym of an expression also does not occur in the
original expression.

|#

(define-library (owl gensym)

   (export
      fresh
      gensym)

   (import
      (owl core)
      (owl symbol)
      (owl string)
      (only (owl syscall) error)
      (owl list)
      (owl tuple)
      (owl render)
      (owl proof)
      (owl math integer))

   (begin

      ; return the gensym id of exp (number) or #false

      (define (between? a x b)
         (and (< a x)
              (< x b)))

      (define (count-gensym-id str pos end n)
         (if (= pos end)
            n
            (let ((this (ref str pos)))
               (cond
                  ((between? 47 this 58)
                     (count-gensym-id str (+ pos 1) end (+ (* n 10) (- this 48))))
                  (else #false)))))

      (define (gensym-id exp)
         (if (symbol? exp)
            (let ((str (symbol->string exp)))
               (let ((len (string-length str)))
                  (if (and (> len 1) (eq? (ref str 0) 103))
                     (count-gensym-id str 1 len 0)
                     #false)))
            #false))

      (define (max-gensym-id exp max)
         (cond
            ((pair? exp)
               (if (eq? (car exp) 'quote)
                  max
                  (max-gensym-id (cdr exp)
                     (max-gensym-id (car exp) max))))
            ((gensym-id exp) =>
               (λ (id) (if (> id max) id max)))
            (else max)))

      (define (max-ast-id exp max)
         (tuple-case exp
            ((var sym)
               (max-gensym-id sym max))
            ((lambda formals body)
               (max-ast-id body
                  (max-gensym-id formals max)))
            ((lambda-var fixed? formals body)
               (max-ast-id body
                  (max-gensym-id formals max)))
            ((call rator rands)
               (max-ast-id rator
                  (fold
                     (λ (max exp) (max-ast-id exp max))
                     max rands)))
            ((value val) max)
            ((receive op fn)
               (max-ast-id op
                  (max-ast-id fn max)))
            ((branch kind a b then else)
               (max-ast-id a (max-ast-id b
                  (max-ast-id then (max-ast-id else max)))))
            ((values vals)
               (fold (λ (max exp) (max-ast-id exp max)) max vals))
            (else
               (error "gensym: max-ast-id: what is this: " exp))))


      (define (gensym exp)
         (lets
            ((id (+ 1 (if (tuple? exp) (max-ast-id exp 0) (max-gensym-id exp 0))))
             (digits (cons 103 (render id #n))))
            (string->symbol (runes->string digits))))

      (define (fresh free)
         (values free (gensym free)))

      (example
         (gensym 'x) = 'g1
         (gensym 'g1) = 'g2
         (gensym '(lambda (x) x)) = 'g1
         (gensym '(lambda (g10) g11)) = 'g12))

)
