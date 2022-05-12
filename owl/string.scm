#| doc
Strings

|#


(define-library (owl string)

   (export
      string?
      string-length
      runes->string      ; code point list (ints) -> string
      bytes->string      ; UTF-8 encoded byte list -> string
      string->bytes      ; string -> list of UTF-8 bytes
      string->runes      ; string -> list of unicode code points
      list->string       ; aka runes->string
      string->list       ; aka string->runes
      string-append
      string-concatenate ; list of strings -> string
      c-string           ; str → #false | UTF-8 encoded null-terminated raw data string
      null-terminate     ; see ^
      finish-string      ; useful to construct a string with sharing
      render-string
      render-quoted-string
      str-iter           ; "a .. n" -> lazy (a .. n) list
      str-iterr          ; "a .. n" -> lazy (n .. a) list
      str-fold           ; fold over code points, as in lists
      str-foldr          ; ditto
      str-iter-bytes     ; "a .. n" -> lazy list of UTF-8 encoded bytes
      str-replace        ; str pat value -> str' ;; todo: drop str-replace, we have regexen now
      string-map         ; op str → str'
      str-rev
      string             ; (string char ...) → str
      string-copy        ; id
      substring          ; str start end → str'
      string-ref         ; str pos → char | error
      string=?           ; str str → bool
      string<?           ; str str → bool
      string>?           ; str str → bool
      string<=?          ; str str → bool
      string>=?          ; str str → bool
      string-ci=?        ; str str → bool
      string-ci<?        ; str str → bool
      string-ci>?        ; str str → bool
      string-ci<=?       ; str str → bool
      string-ci>=?       ; str str → bool
      unicode-fold-char  ; char tail → (char' ... tail)
      make-string        ; n char → str
      )

   (import
      (owl core)
      (owl iff)
      (only (owl syscall) error)
      (owl unicode)
      (owl list)
      (owl list-extra)
      (owl tuple)
      (owl lazy)
      (owl math))

   (include "owl/unicode-char-folds.scm")

   (begin

      (define (string? x)
         (case (type x)
            (type-string #true)
            (type-string-wide #true)
            (type-string-dispatch #true)
            (else #false)))

      (define (string-length str)
         (case (type str)
            (type-string          (sizeb str))
            (type-string-wide     (tuple-length str))
            (type-string-dispatch (ref str 1))
            (else (error "string-length: not a string: " str))))

      ;;; enumerate code points forwards

      (define (str-iter-leaf str tl pos end)
         (if (eq? pos end)
            tl
            (pair (ref str pos)
               (lets ((pos _ (fx+ pos 1)))
                  (str-iter-leaf str tl pos end)))))

      (define (str-iter-wide-leaf str tl pos)
         (if (eq? pos (tuple-length str))
            (cons (ref str pos) tl)
            (pair (ref str pos)
               (lets ((pos _ (fx+ pos 1)))
                  (str-iter-wide-leaf str tl pos)))))

      (define (str-iter-any str tl)
         (case (type str)
            (type-string
               (let ((len (string-length str)))
                  (if (eq? len 0)
                     tl
                     (str-iter-leaf str tl 0 len))))
            (type-string-wide
               (str-iter-wide-leaf str tl 1))
            (type-string-dispatch
               (let loop ((pos 2))
                  (if (eq? pos (tuple-length str))
                     (str-iter-any (ref str pos) tl)
                     (str-iter-any (ref str pos)
                        (λ () (loop (+ pos 1)))))))
            (else
               (error "str-iter: not a string: " str))))

      (define str-iter (C str-iter-any #n))

      ;;; iterate backwards

      (define (str-iterr-leaf str tl pos)
         (if (eq? pos 0)
            (cons (ref str pos) tl)
            (pair (ref str pos)
               (lets ((pos _ (fx- pos 1)))
                  (str-iterr-leaf str tl pos)))))

      (define (str-iterr-wide-leaf str tl pos)
         (if (eq? pos 1)
            (cons (ref str pos) tl)
            (pair (ref str pos)
               (lets ((pos _ (fx- pos 1)))
                  (str-iterr-wide-leaf str tl pos)))))

      (define (str-iterr-any str tl)
         (case (type str)
            (type-string
               (let ((len (string-length str)))
                  (if (eq? len 0)
                     tl
                     (str-iterr-leaf str tl (- len 1)))))
            (type-string-wide
               (str-iterr-wide-leaf str tl (tuple-length str)))
            (type-string-dispatch
               (let loop ((pos (tuple-length str)))
                  (if (eq? pos 2)
                     (str-iterr-any (ref str 2) tl)
                     (str-iterr-any (ref str pos)
                        (λ () (loop (- pos 1)))))))
            (else
               (error "str-iterr: not a string: " str))))

      (define str-iterr (C str-iterr-any #n))

      ;; string folds

      (define (str-fold  op st str) (lfold  op st (str-iter  str)))
      (define (str-foldr op st str) (lfoldr op st (str-iterr str)))

      ;; list conversions

      (define (hexencode cp tl)
         (ilist #\\ #\x
            (append (render-number cp #n 16)
               (cons #\; tl))))

      (define (maybe-hexencode char tl)
         (cond
            ((< char #\space)
               (hexencode char tl))
            ((eq? char 128)
               (hexencode char tl))
            (else
               #false)))

      ;; quote just ":s for now
      (define (encode-quoted-point p tl)
         (cond
            ((eq? p #\")
               (ilist #\\ p tl))
            ((eq? p #\\)
               (ilist #\\ p tl))
            ((eq? p #\newline)
               (ilist #\\ #\n tl))
            ((eq? p #\return)
               (ilist #\\ #\r tl))
            ((eq? p #\tab)
               (ilist #\\ #\t tl))
            ((maybe-hexencode p tl) => self)
            (else
               (encode-point p tl))))

      ; note: it is assumed string construction has checked that all code points are valid and thus encodable
      (define (string->bytes str)    (str-foldr encode-point #n str))
      (define (render-string str tl) (str-foldr encode-point tl str))
      (define (string->runes str)    (str-foldr cons #n str))
      (define (render-quoted-string str tl)
         (str-foldr encode-quoted-point tl str))


      ;; making strings (temp)

      (define (finish-string chunks)
         (let ((n (length chunks)))
            (cond
               ((eq? n 1)
                  (car chunks))
               ((> n 4)
                  ; use 234-nodes for now
                  (lets
                     ((q (>> n 2))
                      (a l (split-at chunks q))
                      (b l (split-at l q))
                      (c d (split-at l q))
                      (subs (map finish-string (list a b c d)))
                      (len (fold + 0 (map string-length subs))))
                     (listuple type-string-dispatch 5 (cons len subs))))
               (else
                  (listuple type-string-dispatch (+ n 1)
                     (cons (fold + 0 (map string-length chunks)) chunks))))))

      (define (make-chunk rcps len ascii?)
         (if ascii?
            (let ((str (raw (reverse rcps) type-string)))
               (if str
                  str
                  (error "Failed to make string: " rcps)))
            (listuple type-string-wide len (reverse rcps))))

      ;; ll|list out n ascii? chunk → string | #false
      (define (stringify runes out n ascii? chu)
         (cond
            ((null? runes)
               (finish-string
                  (reverse (cons (make-chunk out n ascii?) chu))))
            ; make 4Kb chunks by default
            ((eq? n 4096)
               (stringify runes #n 0 #t
                  (cons (make-chunk out n ascii?) chu)))
            ((pair? runes)
               (cond
                  ((and ascii? (< 128 (car runes)) (> n 256))
                     ; allow smaller leaf chunks
                     (stringify runes #n 0 #t
                        (cons (make-chunk out n ascii?) chu)))
                  ((valid-code-point? (car runes))
                     (let ((rune (car runes)))
                        (stringify (cdr runes) (cons rune out) (+ n 1)
                           (and ascii? (< rune 128))
                           chu)))
                  (else #false)))
            (else (stringify (runes) out n ascii? chu))))

      ;; (codepoint ..) → string | #false
      (define (runes->string lst)
         (stringify lst #n 0 #t #n))

      (define bytes->string
         (B runes->string utf8-decode))

      (define (string-concatenate lst)
         (bytes->string (foldr render-string #n lst)))

      (define (string-append . lst)
         (string-concatenate lst))

      (define (string-eq-walk a b)
         (cond
            ((pair? a)
               (cond
                  ((pair? b)
                     (if (= (car a) (car b))
                        (string-eq-walk (cdr a) (cdr b))
                        #false))
                  ((null? b) #false)
                  (else
                     (let ((b (b)))
                        (if (and (pair? b) (= (car b) (car a)))
                           (string-eq-walk (cdr a) (cdr b))
                           #false)))))
            ((null? a)
               (cond
                  ((pair? b) #false)
                  ((null? b) #true)
                  (else (string-eq-walk a (b)))))
            (else (string-eq-walk (a) b))))

      (define (string=? a b)
         (let ((la (string-length a)))
            (if (= (string-length b) la)
               (string-eq-walk (str-iter a) (str-iter b))
               #false)))

      (define string->list string->runes)
      (define list->string runes->string)

      (define-syntax string
         (syntax-rules ()
            ((string . things)
               (list->string (list . things)))))

      (define (c-string str) ; -> bvec | #false
         (raw
            (str-foldr
            ;; do not re-encode raw strings. these are normally ASCII strings
            ;; which would not need encoding anyway, but explicitly bypass it
            ;; to allow these strings to contain *invalid string data*. This
            ;; allows bad non UTF-8 strings coming for example from command
            ;; line arguments (like paths having invalid encoding) to be used
            ;; for opening files.
               (if (eq? (type str) type-string)
                  cons
                  encode-point)
               '(0) str)
            type-string))

      (define null-terminate c-string)

      ;; a naive string replace. add one of the usual faster versions and
      ;; basic regex matching later (maybe that one to lib-lazy instead?)
      ;; but even a slow one will do for now because it is needd for dumping
      ;; sources.

      ;; todo: let l be a lazy list and iterate with it over whatever
      ;; todo: regex matcher would be fun to write. regular languages ftw.

      ; -> #false | tail after p
      (define (grab l p)
         (cond
            ((null? p) l)
            ((null? l) #false)
            ((eq? (car l) (car p)) (grab (cdr l) (cdr p)))
            (else #false)))

      ; O(nm), but irrelevant for current use
      (define (replace-all lst pat val)
         (define rval (reverse val))
         (define (walk rout in)
            (cond
               ((null? in)
                  (reverse rout))
               ((grab in pat) =>
                  (λ (in) (walk (append rval rout) in)))
               (else
                  (walk (cons (car in) rout) (cdr in)))))
         (walk #n lst))

      (define (str-replace str pat val)
         (runes->string
            (replace-all
               (string->runes str)
               (string->runes pat)
               (string->runes val))))

      (define (string-map op str)
         (runes->string
            (lmap op (str-iter str))))

      (define str-rev
         (B runes->string str-iterr))

      (define string-copy self)

      ;; going as per R5RS
      (define (substring str start end)
         (cond
            ((< (string-length str) end)
               (error "substring: out of string: " end))
            ((negative? start)
               (error "substring: negative start: " start))
            ((< end start)
               (error "substring: bad interval " (cons start end)))
            (else
               (list->string (ltake (ldrop (str-iter str) start) (- end start))))))

      ;; lexicographic comparison with end of string < lowest code point
      ;; 1 = sa smaller, 2 = equal, 3 = sb smaller
      (define (str-compare cook sa sb)
         (let loop ((la (cook (str-iter sa))) (lb (cook (str-iter sb))))
            (lets
               ((a la (uncons la #false))
                (b lb (uncons lb #false)))
               (cond
                  ((not a) (if b 1 2))
                  ((not b) 3)
                  ((< a b) 1) ;; todo: lesser? and eq? after they are interned
                  ((= a b) (loop la lb))
                  (else 3)))))

      ;; iff of codepoint → codepoint | (codepoint ...), the first being equal to (codepoint)
      (define char-fold-iff
         (fold
            (λ (iff node)
               (if (= (length node) 2)
                  (iput iff (car node) (cadr node))
                  (iput iff (car node) (cdr node))))
            iempty char-folds))

      (define (unicode-fold-char codepoint tail)
         (let ((mapping (iget char-fold-iff codepoint codepoint)))
            (if (pair? mapping) ;; mapped to a list
               (append mapping tail)
               (cons mapping tail)))) ;; self or changed


      ;; fixme: O(n) temp string-ref! walk the tree later
      (define (string-ref str p)
         (llref (str-iter str) p))

      (define (upcase ll)
         (lets
            ((cp ll (uncons ll #false)))
            (if cp
               (let ((cp (iget char-fold-iff cp cp)))
                  (if (pair? cp)
                     (append cp (upcase ll))
                     (pair cp (upcase ll))))
               #n)))

      (define (string-ci=? a b) (eq? 2 (str-compare upcase a b)))

      (define (string<? a b)       (eq? (str-compare self a b) 1))
      (define (string<=? a b) (not (eq? (str-compare self a b) 3)))
      (define (string>? a b)       (eq? (str-compare self a b) 3))
      (define (string>=? a b) (not (eq? (str-compare self a b) 1)))

      (define (string-ci<? a b)       (eq? 1 (str-compare upcase a b)))
      (define (string-ci<=? a b) (not (eq? 3 (str-compare upcase a b))))
      (define (string-ci>? a b)       (eq? 3 (str-compare upcase a b)))
      (define (string-ci>=? a b) (not (eq? 1 (str-compare upcase a b))))

      (define (str-iter-bytes str)
         (ledit
            (λ (codepoint tl)
               (if (lesser? codepoint #x80)
                  (cons codepoint tl)
                  (encode-point codepoint tl)))
            (str-iter str)))

      (define (make-string n char)
         (list->string (make-list n char)))
))
