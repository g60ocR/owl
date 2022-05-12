#| doc
Register Transfer Language

Lambdas can have any number of variables. The variables eventually end up
representing virtual machine registers. There are only a fixed number of
registers in the VM, and certain values should be in certain registers at
certain points in evaluation. Therefore we need a transformation from the
AST expression to something closer to bytecode operating on registers. This
format uses a similar tuple structure and is called RTL, short for register
transfer language.

The task of this library is mainly to assign a VM register to each variable
and convert references accordingly.

This module is quite old. The register allocator could be updated at some point,
after which the number of VM registers could be reduced.
|#

(define-library (owl eval rtl)

   (export
      compile)

   (import
      (owl core)
      (owl math)
      (owl list)
      (owl bytevector)
      (only (owl syscall) error)
      (owl function)
      (owl symbol)
      (owl list-extra)
      (owl eval ast)
      (owl lazy)
      (owl sort)
      (owl io)
      (prefix (owl eval data) rtl-)
      (only (owl eval env) primop-of)
      (owl eval assemble)
      (owl eval closure))

   (begin

      (define try-n-perms 1000) ;; how many load permutations to try before evicting more registers

      ; regs = (node ...), biggest id first
      ; node = #(var <sym> id)                   ;; <- convert to sum type
      ;      = #(val <value> id)
      ;      = #(env <regs> id)
      ;      = #(lit <values> id)

      ; [r0 = MCP] [r1 = Clos] [r2 = Env] [r3 = a0, often cont] [r4] ... [rn]

      (define a0 3) ;;; number of first argument register (may change)

      (define (next-free-register regs)
         (if (null? regs)
            a0
            (+ (ref (car regs) 3) 1)))

      ; get index of thing at (future) tuple
      ; lst = (l0 l1 ... ln) -> #(header <code/proc> l0 ... ln)
      (define (index-of thing lst pos)
         (cond
            ((null? lst) #false)
            ((eq? (car lst) thing) pos)
            (else (index-of thing (cdr lst) (+ pos 1)))))

      (define (find-any regs sym type subtype)
         (if (null? regs)
            #false
            (let ((this (car regs)))
               (cond
                  ((and (eq? type (ref this 1))
                     (eq? (ref this 2) sym))
                     (ref this 3))
                  ((eq? subtype (ref this 1))
                     (or
                        (find-any (cdr regs) sym type subtype)
                        (let
                           ((sub
                              (index-of sym (ref this 2) 2)))
                           ;; FIXME, 2 will not be correct for shared envs
                           (if sub
                              (cons (ref this 3) sub)
                              #false))))
                  (else
                     (find-any (cdr regs) sym type subtype))))))

      ;; find which register has the literals-tuple
      (define (find-literals env)
         (if (null? env)
            (error "No literals found: " env)
            (tuple-case (car env)
               ((lit vals id)
                  id)
               (else
                  (find-literals (cdr env))))))

      ;; find a register or an env address containing the thing
      (define (find-variable regs var)
         (find-any regs var 'var 'env))

      ;; find a register or address to literals where it can be found
      (define (find-value regs var)
         (find-any regs var 'val 'lit))

      (define (rtl-value regs val cont)
         (let ((position (find-value regs val)))
            (cond
               ((fixnum? position)
                  (cont regs position))
               ((small-value? val)
                  (let ((reg (next-free-register regs)))
                     (rtl-ld val reg
                        (cont (cons (tuple 'val val reg) regs) reg))))
               ((not position)
                  (error "rtl-value: cannot make a load for a " val))
               ((fixnum? (cdr position))
                  (let ((this (next-free-register regs)))
                     (rtl-refi (car position) (cdr position) this
                        (cont (cons (tuple 'val val this) regs) this))))
               (else
                  (error "tried to use old chain load in " val)))))

      (define (rtl-variable regs sym cont)
         (let ((position (find-variable regs sym)))
            (cond
               ((fixnum? position)
                  (cont regs position))
               ((not position)
                  (error "rtl-variable: cannot find the variable " sym))
               ((fixnum? (cdr position))
                  (let ((this (next-free-register regs)))
                     (rtl-refi (car position) (cdr position) this
                        (cont (cons (tuple 'var sym this) regs) this))))
               (else
                  (error "no chain load: " position)))))


      (define (rtl-close regs lit-offset env lit cont)
         (let ((this (next-free-register regs)))
            (cond
               ((null? env)
                  ;; no need to close, just refer the executable procedure
                  (rtl-refi (find-literals regs) lit-offset this
                     (cont
                        (cons (tuple 'val (list 'a-closure) this) regs)
                        this)))
               ((null? lit)
                  ;; the function will be of the form
                  ;; #(closure-header <code> e0 ... en)
                  (rtl-cons-close #false (find-literals regs) lit-offset env this
                     (cont
                        (cons (tuple 'val (list 'a-closure) this) regs)
                        this)))
               (else
                  ;; the function will be of the form
                  ;; #(clos-header #(proc-header <code> l0 .. ln) e0 .. em)
                  (rtl-cons-close #true (find-literals regs) lit-offset env this
                     (cont
                        (cons (tuple 'val (list 'a-closure) this) regs)
                        this))))))

      (define (env->loadable env)
         (map
            (λ (x)
               (if (symbol? x)
                  (tuple 'var x)
                  (error "Cannot yet load this env node: " env)))
            env))

      (define (create-alias regs name position)
         (let ((this (car regs)))
            (if (eq? (ref this 3) position)
               (cons (tuple 'var name position) regs)
               (cons this
                  (create-alias (cdr regs) name position)))))

      (define (create-aliases regs names positions)
         (fold (λ (regs alias) (create-alias regs (car alias) (cdr alias)))
            regs (zip cons names positions)))

      (define (rtl-arguments one?)

         (define (one regs a cont)
            (tuple-case a
               ((value val)
                  (rtl-value regs val cont))
               ((var sym)
                  (rtl-variable regs sym cont))
               ((make-closure lpos env lit)
                  (many regs (env->loadable env) #n
                     (λ (regs envp)
                        (rtl-close regs lpos envp lit cont))))
               (else
                  (error "rtl-simple: unknown thing: " a))))

         (define (many regs args places cont)
            (if (null? args)
               (cont regs (reverse places))
               (one regs (car args)
                  (λ (regs pos)
                     (many regs (cdr args) (cons pos places) cont)))))
         (if one?
            one
            (λ (regs args cont)
               (many regs args #n cont))))


      (define rtl-simple (rtl-arguments #true))

      (define rtl-args (rtl-arguments #false))

      ; -> [reg] + regs'
      (define (rtl-bind regs formals)
         (let loop ((regs regs) (formals formals) (taken #n))
            (if (null? formals)
               (tuple (reverse taken) regs)
               (let ((this (next-free-register regs)))
                  (loop
                     (cons (tuple 'var (car formals) this) regs)
                     (cdr formals)
                     (cons this taken))))))

      ;; fixme: mkt chugs the type to the instruction
      (define (rtl-primitive regs op formals args cont)
         (if (eq? op 23) ; generalize this later. mkt is not a safe instruction!
            (if (null? args)
               (error "rtl-primitive: no type for mkt" args)
               (rtl-primitive regs
                  (fxior (<< op 8) (band (value-of (car args)) #xff))
                  formals (cdr args) cont))
            (rtl-args regs args
               (λ (regs args)
                  ;; args = input registers
                  (cond
                     ;; a run-of-the-mill a0 .. an → rval -primop
                     ((and (= (length formals) 1) (not (special-bind-primop? op)))
                        (let ((this (next-free-register regs)))
                           (rtl-prim op args this
                              (cont
                                 (cons
                                    (tuple 'var (car formals) this)
                                    regs)))))
                     (else
                        ; bind or ff-bind, or arithmetic
                        (bind (rtl-bind regs formals)
                           (λ (selected regs)
                              (rtl-prim op args selected
                                 (cont regs))))))))))


      (define (rtl-make-moves sequence tail)
         (foldr
            (λ (move rest)
               (if (eq? (car move) (cdr move))
                  rest
                  (rtl-move (car move) (cdr move) rest)))
            tail sequence))

      (define (rtl-moves-ok? moves)
         (cond
            ((null? moves) #true)
            ((assq (cdar moves) (cdr moves))
               #false)
            (else
               (rtl-moves-ok? (cdr moves)))))

      ;;; (from ...) -> ((from . to) ...)
      (define (rtl-add-targets args)
         (zip cons args
            (iota a0 1 (+ (length args) a0))))

      (define (rtl-safe-registers n call)
         (let loop
            ((hp (+ (length call) (+ a0 1)))
             (safe #n)
             (n n))
            (cond
               ((= n 0)
                  (reverse safe))
               ((memq hp call)
                  (loop (+ hp 1) safe n))
               (else
                  (loop (+ hp 1) (cons hp safe) (- n 1))))))

      ;;; -> replace the to-save registers in call
      (define (apply-saves to-save safes call)
         (let ((new (zip cons to-save safes)))
            (map
               (λ (reg)
                  (let ((node (assq reg new)))
                     (if node (cdr node) reg)))
               call)))

      (define (rtl-check-moves perms n)
         (call/cc
            (λ (ret)
               (lfor 0 perms
                  (λ (nth perm)
                     (cond
                        ((rtl-moves-ok? perm) (ret perm))
                        ((eq? nth try-n-perms) (ret #false))
                        (else (+ nth 1)))))
                  #false)))

      ;;; find the first set of saves that works
      (define (rtl-try-saves saves free call rest)
         (lets
            ((call-prime (apply-saves saves free call))
             (call-prime (rtl-add-targets call-prime))
             (call-prime
               (remove
                  (λ (move) (eq? (car move) (cdr move)))
                  call-prime))
             (call-prime (sort (λ (a b) (< (car a) (car b))) call-prime))
             (perms (permutations call-prime))
             (ok-moves (rtl-check-moves perms 1)))
            (if ok-moves
               (rtl-make-moves
                  (append (zip cons saves free) ok-moves)
                  rest)
               #false)))

      (define (rtl-make-jump call free rest)
         (call/cc
            (λ (ret)
               (or
                  (lfor #false (subsets call)
                     (λ (foo subset)
                        (cond
                           ((rtl-try-saves subset free call rest) => ret)
                           (else #false))))
                  ; has never happened in practice
                  (error "failed to compile call: " call)))))

      (define (maybe-arity obj)
         (let ((op (ref obj 0)))
            (if (eq? op 60) ;; fixed arity, new instruction
               (ref obj 1)
               #false)))    ;; variable or something else

      (define (validate-arity obj incoming code)
         (let ((arity (maybe-arity obj)))
            (cond
               ((not arity) 
                  ;; it's like asking what are birds
                  #false) 
               ((eq? arity incoming)
                  #true)
               (else
                  (error "invalid call" (list obj " would get " incoming " instead of " arity " arguments"))))))
              
      ;; fail if definitely error 
      (define (check-arity rator n)
         (tuple-case rator
            ((value obj)
               (let ((t (type obj)))
                  (cond
                     ((eq? type-bytecode t) ;; raw bytecode
                        (validate-arity obj n obj)) 
                     ((eq? t type-proc)
                        (validate-arity obj n (ref obj 1))) 
                     ((eq? t type-clos)
                        (validate-arity obj n (ref (ref obj 1) 1))) 
                     (else
                        (error obj "would end up being called as a function.")))))
            (else 
               ;; insufficient time for a meaningful answer at compile time
               #t)))

      (define (rtl-jump rator rands free inst)
         (let ((nargs (length rands)))
            (check-arity rator nargs)
            (cond
               ;; cont is usually at 3, and usually there is
               ;; 1 return value -> special instruction
               ((and (eq? rator a0) (= nargs 1))
                  (rtl-ret (car rands)))
               ;;; rator is itself in rands, and does not need rescuing
               ((memq rator rands)
                  (rtl-make-jump rands free
                     (inst (index-of rator rands a0) nargs)))
               ;;; rator is above rands, again no need to rescue
               ((> rator (+ 2 nargs))
                  (rtl-make-jump rands free
                     (if inst
                        (inst rator nargs)
                        (rtl-goto rator (length rands)))))
               (else
                  (rtl-move rator (car free)
                     (rtl-jump (car free) rands (cdr free) inst))))))


      (define (rtl-call regs rator rands)
         ; rator is here possibly #(value #<func>) and much of the call can be inlined
         ; change the flag if can check call here
         (rtl-args regs (cons rator rands)
            (λ (regs all)
               (let ((free (rtl-safe-registers (length all) all)))
                  (rtl-jump (car all) (cdr all) free rtl-goto)))))

      (define (value-simple? val)
         (tuple-case val
            ((value val) (simple-value? val))
            (else #f)))

      (define (simple-first a b cont)
         (if (value-simple? b)
            (cont b a)
            (cont a b)))

      (define (extract-value node)
         (tuple-case node
            ((value val) val)
            (else #false)))


      ;; compile any AST node node to RTL
      (define (rtl-any regs exp)
         (tuple-case exp
            ((branch kind a b then else)
               (cond
                  ((eq? kind 0)      ; branch on equality (jump if equal)
                     (simple-first a b
                        ;;; move simple to a, if any
                        (λ (a b)
                           (if-lets ((i (value-simple? a)))
                              (rtl-simple regs b
                                 (λ (regs bp)
                                    (let
                                       ((then (rtl-any regs then))
                                        (else (rtl-any regs else)))
                                       (rtl-jeqi i bp then else))))
                              (rtl-simple regs a
                                 (λ (regs ap)
                                    (rtl-simple regs b (λ (regs bp)
                                       (let
                                          ((then (rtl-any regs then))
                                           (else (rtl-any regs else)))
                                          (rtl-jeq ap bp then else))))))))))
                  (else
                     (error "rtl-any: unknown branch type: " kind))))
            ((call rator rands)
               ;; compile as primop call, bind if rator is lambda or a generic call
               (let ((op (and (eq? (ref rator 1) 'value) (primop-of (ref rator 2)))))
                  (if op
                     (tuple-case (car rands)
                        ((lambda-var fixed? formals body)
                           (if (and fixed? (opcode-arity-ok? op (length (cdr rands))))
                              (rtl-primitive regs op formals (cdr rands)
                                 (C rtl-any body))
                              ;; fixme: should be a way to show just parts of AST nodes, which may look odd
                              (error "Bad number of arguments for primitive: "
                                 (list 'op (primop-name op) 'got (length (cdr rands)) 'arguments))))
                        (else
                           (error "bad primitive args: " rands)))
                     (tuple-case rator
                        ((lambda-var fixed? formals body)
                           ;; ((lambda (args) ...) ...) => add new aliases for values
                           (if fixed?
                              (rtl-args regs rands
                                 (λ (regs args)
                                    ;;; note that this is an alias thing...
                                    (if (= (length formals) (length args))
                                       (rtl-any (create-aliases regs formals args) body)
                                       (error "Bad argument count in lambda call: " (list 'args args 'formals formals)))))
                              (rtl-call regs rator rands)))
                        (else
                           (rtl-call regs rator rands))))))
            (else
               (error "rtl-any: wtf: " exp))))

      (define (formals->regs formals pos)
         (if (null? formals)
            #n
            (cons (tuple 'var (car formals) pos)
               (formals->regs (cdr formals) (+ pos 1)))))

      ; r0 = mcp, r1 = clos, r2 = lit, r3 aka a0 = arg0, r4 = arg1, ...

      (define (entry-regs clos literals formals)
         (append
            (reverse (formals->regs formals a0))
            (if (null? clos)
               (list
                  (tuple 'env #n 2)          ; <- really just empty
                  (tuple 'lit literals 1))   ; <- may be empty
               (list
                  (tuple 'lit literals 2)    ; <- may be empty
                  (tuple 'env clos 1)))))

      ;;; closure -> executable procedure (closed from elsewhere if not independent)

      (define (rtl-literal rtl thing)
         (if (uncompiled-closure? thing)
            (rtl (cdr thing))
            thing))

      ; code .. → code' ...
      (define (rtl-literals rtl-procedure lits)
         ;;; convert all uncompiled closures to procedures
         (map (H rtl-literal rtl-procedure) lits))

      (define (list->proc lst)
         (listuple type-proc (length lst) lst))

      ;; rtl-procedure now passes the intended new form here - replace it later in the AST node also
      (define (rtl-plain-lambda rtl exp clos literals tail)
         (tuple-case exp
            ((lambda-var fixed? formals body)
               (let
                  ((exec
                     (assemble-code
                        (tuple 'code-var fixed?
                           (length formals)
                           (rtl-any (entry-regs clos literals formals) body))
                        tail)))
                  (if (null? literals)
                     exec ; #<bytecode>
                     (list->proc (cons exec literals)))))
            (else
               (error "rtl-plain-lambda: bad node " exp))))

      ;;; proc = #(procedure-header <code-ptr> l0 ... ln)
      ; env node → env' owl-func
      (define (rtl-procedure node)
         (tuple-case node
            ((closure-var fixed? formals body clos literals)
               (rtl-plain-lambda rtl-procedure
                  (tuple 'lambda-var fixed? formals body)
                  clos (rtl-literals rtl-procedure literals) #n))
            (else
               (error "rtl-procedure: bad input: " node))))

      ; exp → exp'
      (define (rtl-exp exp)
         (tuple-case exp
            ((closure-var fixed? formals body clos literals)
               (if (null? clos)
                  (rtl-procedure exp)
                  (error "rtl-exp: free variables in entry closure: " clos)))
            (else
               #false)))

      ;; todo: exit via fail cont on errors
      (define (compile exp env)
         (rtl-ok (rtl-exp exp) env))
))
