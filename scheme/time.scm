(define-library (scheme time)

   (import
      (scheme base)
      (only (owl time) time time-ms))

   (export
      current-jiffy
      current-second
      jiffies-per-second)

   (begin

      ;; note: not using clock() and CLOCKS_PER_SEC, because the bytecode must be portable

      (define (jiffies-per-second) 1000)

      (define current-jiffy time-ms)

      (define current-second time)
))
