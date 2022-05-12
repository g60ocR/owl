(define-library (scheme base)
  (export
      *
      +
      -
      ...
      /
      <
      <=
      =
      =>
      >
      >=
      abs
      and
      append
      apply
      assoc
      assq
      assv
      begin
      binary-port?
      boolean=?
      boolean?
      bytevector
      bytevector-append
      bytevector-copy
      bytevector-copy!
      bytevector-length
      bytevector-u8-ref
      bytevector-u8-set!
      bytevector?
      caar
      cadr
      call-with-current-continuation
      call-with-port
      call-with-values
      call/cc
      car
      case
      cdar
      cddr
      cdr
      ceiling
      char->integer
      char-ready?
      char<=?
      char<?
      char=?
      char>=?
      char>?
      char?
      close-input-port
      close-output-port
      close-port
      complex?
      cond
      cons
      current-error-port
      current-input-port
      current-output-port
      define
      define-library
      define-record-type
      define-syntax
      define-values
      denominator
      do
      dynamic-wind
      else
      eof-object
      eof-object?
      eq?
      equal?
      eqv?
      error
      error-object-irritants
      error-object-message
      error-object?
      even?
      exact
      exact-integer-sqrt
      exact-integer?
      exact?
      expt
      features
      file-error?
      floor
      floor-quotient
      floor-remainder
      floor/
      flush-output-port
      for-each
      gcd
      get-output-bytevector
      get-output-string
      guard
      if
      include
      include-ci
      inexact
      inexact?
      input-port-open?
      input-port?
      integer->char
      integer?
      lambda
      lcm
      length
      let
      let*
      let*-values
      let-syntax
      let-values
      letrec
      letrec*
      letrec-syntax
      list
      list->string
      list->vector
      list-copy
      list-ref
      list-set!
      list-tail
      list?
      make-bytevector
      make-list
      make-parameter
      make-string
      make-vector
      map
      max
      member
      memq
      memv
      min
      modulo
      negative?
      newline
      not
      null?
      number->string
      number?
      numerator
      odd?
      open-input-bytevector
      open-input-string
      open-output-bytevector
      open-output-string
      or
      output-port-open?
      output-port?
      pair?
      parameterize
      peek-char
      peek-u8
      port?
      positive?
      procedure?
      quasiquote
      quote
      quotient
      raise
      raise-continuable
      rational?
      rationalize
      read-bytevector
      read-bytevector!
      read-char
      read-error?
      read-line
      read-string
      read-u8
      real?
      remainder
      reverse
      round
      set!
      set-car!
      set-cdr!
      square
      string
      string->list
      string->number
      string->symbol
      string->utf8
      string->vector
      string-append
      string-copy
      string-copy!
      string-fill!
      string-for-each
      string-length
      string-map
      string-ref
      string-set!
      string<=?
      string<?
      string=?
      string>=?
      string>?
      string?
      substring
      symbol->string
      symbol=?
      symbol?
      syntax-error
      textual-port?
      truncate
      truncate-quotient
      truncate-remainder
      truncate/
      u8-ready?
      unless
      unquote
      unquote-splicing
      utf8->string
      values
      vector
      vector->list
      vector->string
      vector-append
      vector-copy
      vector-copy!
      vector-fill!
      vector-for-each
      vector-length
      vector-map
      vector-ref
      vector-set!
      vector?
      when
      with-exception-handler
      write-bytevector
      write-char
      write-string
      write-u8
      zero?
      string->integer ;; NOT R7RS but used currently in many places in owl stuff
      )

   (import
      (owl core)
      (owl syscall)
      (owl eof)
      (owl equal)
      (owl list)
      (only (owl function) procedure?)
      (only (owl ff) get)
      (only (owl syscall) error)
      (only (owl variable) link-variable)
      (owl string)
      (owl math)
      (owl math extra)
      (owl bytevector)
      (owl vector)
      (owl port)
      (only (owl symbol) string->symbol symbol? symbol=? symbol->string)
      (only (owl sexp) list->number)
      (owl list-extra)
      (owl io)
      (owl boolean)
      (owl char))

   (begin

      (define-syntax define-symbols
         (syntax-rules (define-values values)
            ((define-symbols x ...)
               (define-values (x ...)
                  (values (quote x) ...)))))

      (define-symbols ... => else unquote unquote-splicing)

      (define-syntax define-missing-bad
         (syntax-rules ()
            ((define-missing-bad name)
               (define name
                  (lambda args
                     (error "Implementation restriction:" (cons (quote name) args)))))))

      (define call-with-current-continuation call/cc)

      (define features
         (let ((owl-state (link-variable '*state*)))
            (λ () (get (owl-state) 'features '()))))

      ;; grr, scheme member functions don't follow the argument conventions of other functions used in owl...

      (define (member x lst . cmp)
         (find-tail
            (H (if (null? cmp) equal? (car cmp)) x)
            lst))

      (define (memv x lst)
         (member x lst eqv?))

      (define (assoc k lst . cmp)
         (find
            (B (H (if (null? cmp) equal? (car cmp)) k) car)
            lst))

      (define (assv k lst)
         (assoc k lst eqv?))

      ;; just for compatibility, as lists are always immutable in owl
      (define list-copy self)

      (define make-bytevector
         (case-lambda
            ((n)
               (list->bytevector (make-list n 0)))
            ((n val)
               (list->bytevector (make-list n val)))))

      (define floor-remainder modulo)
      (define truncate-quotient quotient)
      (define truncate-remainder remainder)

      ;; owl doesn't have inexact numbers, so any argument
      ;; coming in will always be rational differing by 0
      (define rationalize K)

      (define (exact? n) #t)
      (define (inexact? n) #f)
      (define exact self)
      (define inexact self)
      (define exact-integer? integer?)

      (define (string-for-each proc str)
         (str-fold (λ (_ c) (proc c)) #t str))

      (define string->number
         (case-lambda
            ((str base)
               (list->number (string->list str) base))
            ((str)
               (list->number (string->list str) 10))))

      (define (string->integer str)
         (let ((n (string->number str 10)))
            (and (integer? n) n)))

      (define (number->string/base n base)
         (list->string (render-number n '() base)))

      (define number->string
         (case-lambda
            ((n) (number->string/base n 10))
            ((n base) (number->string/base n base))))

      (define (square x) (* x x))

      (define (current-input-port) stdin)
      (define (current-output-port) stdout)
      (define (current-error-port) stderr)

      (define binary-port? port?)
      (define textual-port? port?)

      (define (newline . port)
         (write-bytevector (bytevector #\newline) (if (null? port) stdout (car port))))

      (define-syntax call-with-values
         (syntax-rules ()
            ((call-with-values (lambda () exp) (lambda (arg ...) body))
               (receive exp (lambda (arg ...) body)))
            ((call-with-values thunk (lambda (arg ...) body))
               (receive (thunk) (lambda (arg ...) body)))))

      (define-syntax do
         (syntax-rules (__init)
            ((do __init () ((var init step) ...) (test then ...) command ...)
               (let loop ((var init) ...)
                  (if test
                     (begin then ...)
                     (begin
                        command ...
                        (loop step ...)))))
            ((do __init ((var init step) . rest) done . tail)
               (do __init rest ((var init step) . done) . tail))
            ((do __init ((var init) . rest) done . tail)
               (do __init rest ((var init var) . done) . tail))
            ((do (vari ...) (test exp ...) command ...)
               (do __init (vari ...) () (test exp ...) command ...))))

      (define-syntax let*-values
         (syntax-rules ()
            ((let*-values (((var ...) gen) . rest) . body)
               (receive gen
                  (λ (var ...) (let*-values rest . body))))
            ((let*-values () . rest)
               (begin . rest))))

      (define-syntax let-values
         (syntax-rules ()
            ((let-values . stuff) (let*-values . stuff))))

      (define-syntax let*
         (syntax-rules ()
            ((let* . stuff) (lets . stuff))))

      (define (char-ready? . port)
         (lets
            ((port (if (null? port) stdin (car port)))
             (result (interact 'iomux (tuple 'read-timeout port 1))))
            (not (eq? result 'timeout))))

      (define-missing-bad write-u8)
      (define-missing-bad write-string)
      (define-missing-bad write-char)
      (define-missing-bad with-exception-handler)
      (define-missing-bad vector-set!)
      (define-missing-bad vector-for-each)
      (define-missing-bad vector-fill!)
      (define-missing-bad vector-copy!)
      (define-missing-bad vector-copy)
      (define-missing-bad vector-append)
      (define-missing-bad vector->string)
      (define-missing-bad utf8->string)
      (define-missing-bad u8-ready?)
      (define-missing-bad string-set!)
      (define-missing-bad string-fill!)
      (define-missing-bad string-copy!)
      (define-missing-bad string->vector)
      (define-missing-bad string->utf8)
      (define-missing-bad set-cdr!)
      (define-missing-bad set-car!)
      (define-missing-bad set!)
      (define-missing-bad read-u8)
      (define-missing-bad read-string)
      (define-missing-bad read-line)
      (define-missing-bad read-error?)
      (define-missing-bad read-char)
      (define-missing-bad read-bytevector!)
      (define-missing-bad raise-continuable)
      (define-missing-bad raise)
      (define-missing-bad peek-u8)
      (define-missing-bad peek-char)
      (define-missing-bad parameterize)
      (define-missing-bad output-port?)
      (define-missing-bad output-port-open?)
      (define-missing-bad open-output-string)
      (define-missing-bad open-output-bytevector)
      (define-missing-bad open-input-string)
      (define-missing-bad open-input-bytevector)
      (define-missing-bad make-parameter)
      (define-missing-bad list-set!)
      (define-missing-bad letrec-syntax)
      (define-missing-bad let-syntax)
      (define-missing-bad input-port?)
      (define-missing-bad input-port-open?)
      (define-missing-bad include-ci)
      (define-missing-bad include)
      (define-missing-bad guard)
      (define-missing-bad get-output-string)
      (define-missing-bad get-output-bytevector)
      (define-missing-bad flush-output-port)
      (define-missing-bad floor/)
      (define-missing-bad floor-quotient)
      (define-missing-bad file-error?)
      (define-missing-bad error-object?)
      (define-missing-bad error-object-message)
      (define-missing-bad error-object-irritants)
      (define-missing-bad dynamic-wind)
      (define-missing-bad close-output-port)
      (define-missing-bad close-input-port)
      (define-missing-bad call-with-port)
      (define-missing-bad bytevector-u8-set!)
      (define-missing-bad bytevector-copy!)
      (define-missing-bad define-record-type) ;; to be replaced
))
