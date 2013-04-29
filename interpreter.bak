; ================================
; Author: Sean Fox (saf66)
; To run: (interpret "filename")
; Notes:
;     I'm using DrRacket with #lang set to R5RS.
;     It should pass all tests except for call-by-reference, which is not implemented.
; ================================

; ================================
; Helper Functions

; throw an error
(define (error reason . args)
    (display "Error: ")
    (display reason)
    (for-each (lambda (arg) 
        (display " ")
        (write arg))
    args)
    (newline)
    (scheme-report-environment -1))

; shortcut for call-with-current-continuation
(define call/cc call-with-current-continuation)

; returns true if all elements cause the function to return true, false otherwise
(define all? (lambda (f l)
    (cond
        ((null? l) #t)
        ((not (f (car l))) #f)
        (else (all? f (cdr l)))
    )
))

; ================================
; Entry Point

(load "functionParser.scm")

(define interpret (lambda (file)
    (call/cc (lambda (return)
        (eval-exp
            (append (parser file) (list
               (list 'return (list 'funcall 'main))
            ))
            the-global-env
            return
            (lambda () (error "BREAK: Break called outside a loop!"))
            (lambda () (error "CONTINUE: Continue called outside a loop!"))
        )
    ))
))

; ================================
; Environment

(define the-empty-env (list))

(define make-frame (lambda (vars vals) (cons vars vals)))
(define frame-vars (lambda (frame) (car frame)))
(define frame-vals (lambda (frame) (cdr frame)))
(define set-in-frame! (lambda (var val frame)
    (set-car! frame (make-frame var (frame-vars frame)))
    (set-cdr! frame (make-frame val (frame-vals frame)))
))

(define first-frame (lambda (env) (car env)))
(define parent-env (lambda (env) (cdr env)))
(define extend-env (lambda (vars vals env)
    (cons (make-frame vars vals) env)
))
(define new-frame (lambda (env)
    (extend-env (list) (list) env)
))

(define tagged-list? (lambda (exp tag)
    (if (pair? exp)
        (eq? (car exp) tag)
        #f
    )
))

; ================================
; Variable

(define var? (lambda (exp) (symbol? exp)))
(define var-define? (lambda (exp) (tagged-list? exp 'var)))
(define var-assign? (lambda (exp) (tagged-list? exp '=)))

(define env-loop (lambda (var val env none-cb match-cb)
    (define scan (lambda (vars vals)
        (cond
            ((null? vars) (none-cb vars vals))
            ((eq? var (car vars)) (match-cb vars vals))
            (else (scan (cdr vars) (cdr vals)))
        )
    ))
    (if (eq? env the-empty-env)
        (error "SCAN: Unbound variable:" var)
        (
            (lambda (frame) (scan (frame-vars frame) (frame-vals frame)))
            (first-frame env)
        )
    )
))

(define new-var! (lambda (var val env)
    (
        (lambda (frame)
            (define scan (lambda (vars vals)
                (cond
                    ((null? vars)
                        (set-in-frame! var val frame)
                        val
                    )
                    ((eq? var (car vars))
                        (set-car! vals val)
                        val
                    )
                    (else (scan (cdr vars) (cdr vals)))
                )
            ))
            (scan (frame-vars frame) (frame-vals frame))
        )
        (first-frame env)
    )
))

(define get-var (lambda (var env)
    (env-loop var (list) env
        (lambda (vars vals) (get-var var (parent-env env)))
        (lambda (vars vals) (car vals))
    )
))

(define set-var! (lambda (var val env)
    (env-loop var (list) env
        (lambda (vars vals) (set-var! var val (parent-env env)))
        (lambda (vars vals) (set-car! vals val))
    )
    val
))

(define del-var! (lambda (var env)
    (env-loop var (list) env
        (lambda (vars vals) (del-var! var (parent-env env)))
        (lambda (vars vals)
            (set-car! vars (list))
            (set-car! vals (list))
        )
    )
))

(define var-exist? (lambda (var env)
    (define scan (lambda (vars vals)
        (cond
            ((null? vars) (var-exist? var (parent-env env)))
            ((eq? var (car vars)) #t)
            (else (scan (cdr vars) (cdr vals)))
        )
    ))
    (if (eq? env the-empty-env)
        #f
        (
            (lambda (frame) (scan (frame-vars frame) (frame-vals frame)))
            (first-frame env)
        )
    )
))

(define copy-vars! (lambda (vars source-env target-env)
    (cond
        ((null? vars) target-env)
        (else
            (new-var! (car vars) (get-var (car vars) source-env) target-env)
            (copy-vars! (cdr vars) source-env target-env)
        )
    )
))

; ================================
; Primitive

(define prim-procs
    (list
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list '% modulo)
        (list '== eqv?)
        (list '!= (lambda (x y) (not (eqv? x y))))
        (list '< <)
        (list '> >)
        (list '<= <=)
        (list '>= >=)
        (list '&& (lambda (x y) (and x y)))
        (list '|| (lambda (x y) (or x y)))
        (list '! not)
    )
)

(define make-prim (lambda (body) (list 'primitive body)))
(define prim? (lambda (proc) (tagged-list? proc 'primitive)))
(define prim-body (lambda (proc) (cadr proc)))

(define prim-vars (lambda () (map car prim-procs)))
(define prim-refs (lambda ()
    (map (lambda (proc) (make-prim (prim-body proc))) prim-procs)
))

(define apply-prim (lambda (proc args)
    (apply (prim-body proc) args)
))

; ================================
; Setup Environment

(define setup-env (lambda ()
    (
        (lambda (env)
            (new-var! 'true #t env)
            (new-var! 'false #f env)
            env
        )
        (extend-env
            (prim-vars)
            (prim-refs)
            the-empty-env
        )
    )
))
(define the-global-env (setup-env))

; ================================
; Boolean Logic

(define false? (lambda (bool) (eq? bool #f)))
(define true? (lambda (bool) (not (false? bool))))

; ================================
; Statement

(define statement? (lambda (exp) (pair? exp)))
(define operator (lambda (exp) (car exp)))
(define operands (lambda (exp) (cdr exp)))

(define eval-operands (lambda (ops env return break continue)
    (map (lambda (exp) (eval-exp exp env return break continue)) ops)
))
(define eval-statement (lambda (exp env return break continue)
    (apply-proc
        (eval-exp (operator exp) env return break continue)
        (eval-operands (operands exp) env return break continue)
        return break continue
    )
))

; ================================
; Sequence

(define sequence? (lambda (exp)
    (and
        (all? statement? exp)
        (not (null? (operands exp)))
    )
))
(define last-exp? (lambda (seq) (null? (cdr seq))))
(define first-exp (lambda (seq) (car seq)))
(define rest-exps (lambda (seq) (cdr seq)))

(define eval-seq (lambda (seq env return break continue)
    (cond
        ((last-exp? seq) (eval-exp (first-exp seq) env return break continue))
        (else
            (eval-exp (first-exp seq) env return break continue)
            (eval-seq (rest-exps seq) env return break continue)
        )
    )
))

; ================================
; Procedure

(define make-proc (lambda (params body env) (list 'procedure params body env)))
(define proc? (lambda (proc) (tagged-list? proc 'procedure)))
(define proc-params (lambda (proc) (cadr proc)))
(define proc-body (lambda (proc) (caddr proc)))
(define proc-env (lambda (proc) (cadddr proc)))

(define apply-proc (lambda (proc args return break continue)
    (cond
        ((self-eval? proc) proc)
        ((prim? proc) (apply-prim proc args))
        ((proc? proc)
            (eval-seq
                (proc-body proc)
                (extend-env
                    (proc-params proc)
                    args
                    (proc-env proc)
                )
                return break continue
            )
        )
        (else (error "APPLY: Unknown procedure:" proc))
    )
))

; ================================
; Expression

(define eval-exp (lambda (exp env return break continue)
    (cond
        ((self-eval? exp) exp)
        ((var? exp) (get-var exp env))
        ((var-define? exp) (eval-var-define exp env return break continue))
        ((var-assign? exp) (eval-var-assign exp env return break continue))
        ((return? exp) (eval-return exp env return break continue))
        ((break? exp) (break))
        ((continue? exp) (continue))
        ((block? exp) (eval-block exp env return break continue))
        ((conditional? exp) (eval-conditional exp env return break continue))
        ((while? exp) (eval-while exp env return break continue))
        ((method-define? exp) (eval-method-define exp env return break continue))
        ((method-call? exp) (eval-method-call exp env return break continue))
        ;[todo] ...
        ((sequence? exp) (eval-seq exp env return break continue))
        ((statement? exp) (eval-statement exp env return break continue))
        (else (error "EVAL: Unknown expression:" exp))
    )
))

(define self-eval? (lambda (exp)
    (or
        (number? exp)
        (boolean? exp)
        (eq? 'nop exp)
        #f
    )
))

; ================================
; Variable Definition

(define definition-var (lambda (exp) (cadr exp)))
(define definition-val (lambda (exp)
    (if (null? (cddr exp))
        'nop
        (caddr exp)
    )
))
(define assignment-var (lambda (exp) (cadr exp)))
(define assignment-val (lambda (exp) (caddr exp)))

(define eval-var-define (lambda (exp env return break continue)
    (
        (lambda (val)
            (new-var! (definition-var exp) val env)
            val
        )
        (eval-exp (definition-val exp) env return break continue)
    )
))

(define eval-var-assign (lambda (exp env return break continue)
    (
        (lambda (val)
            (set-var! (assignment-var exp) val env)
            val
        )
        (eval-exp (assignment-val exp) env return break continue)
    )
))

; ================================
; Return

(define return? (lambda (exp) (tagged-list? exp 'return)))
(define return-val (lambda (exp) (cadr exp)))

(define eval-return (lambda (exp env return break continue)
    (return (eval-exp (return-val exp) env return break continue))
))

; ================================
; Control Flow

(define break? (lambda (exp) (tagged-list? exp 'break)))
(define continue? (lambda (exp) (tagged-list? exp 'continue)))

; ================================
; Block

(define block? (lambda (exp) (tagged-list? exp 'begin)))
(define block-inner (lambda (exp) (cdr exp)))

(define eval-block (lambda (exp env return break continue)
    (eval-exp (block-inner exp) (new-frame env) return break continue)
))

; ================================
; Conditional

(define conditional? (lambda (exp) (tagged-list? exp 'if)))
(define conditional-predicate (lambda (exp) (cadr exp)))
(define conditional-consequent (lambda (exp) (caddr exp)))
(define conditional-alternative (lambda (exp)
    (if (null? (cdddr exp))
        'nop
        (cadddr exp)
    )
))

(define eval-conditional (lambda (exp env return break continue)
    (if (true? (eval-exp (conditional-predicate exp) env return break continue))
        (eval-exp (conditional-consequent exp) (new-frame env) return break continue)
        (eval-exp (conditional-alternative exp) (new-frame env) return break continue)
    )
))

; ================================
; While Loop

(define while? (lambda (exp) (tagged-list? exp 'while)))
(define while-condition (lambda (exp) (cadr exp)))
(define while-body (lambda (exp) (caddr exp)))

(define eval-while (lambda (exp env return break continue)
    (define eval-while-inner (lambda (exp env return break continue)
        (cond
            ((true? (eval-exp (while-condition exp) env return break continue))
                (call/cc (lambda (continue)
                    (eval-exp (while-body exp) env return break continue)
                ))
                (eval-while-inner exp env return break continue)
            )
            (else 'nop)
        )
    ))
    (call/cc (lambda (break)
        (eval-while-inner exp (new-frame env) return break continue)
    ))
))

; ================================
; Method Definition

(define method-define? (lambda (exp) (tagged-list? exp 'function)))
(define method-name (lambda (exp) (cadr exp)))
(define method-params (lambda (exp) (caddr exp)))
(define method-body (lambda (exp) (cadddr exp)))

(define eval-method-define (lambda (exp env return break continue)
    (new-var! (method-name exp)
        (make-proc
            (method-params exp)
            (method-body exp)
            env
        )
    env)
))

; ================================
; Method Call

(define method-call? (lambda (exp) (tagged-list? exp 'funcall)))
(define method-args (lambda (exp) (cddr exp)))

(define eval-method-call (lambda (exp env return break continue)
    (define update-proc-env (lambda (var env proc)
        (make-proc
            (proc-params proc)
            (proc-body proc)
            (copy-vars! (list var) env (new-frame (proc-env proc)))
        )
    ))
    (call/cc (lambda (return)
        (
            (lambda (name args)
                (if (var-exist? name env)
                    (
                        (lambda (proc)
                            (if (= (length (proc-params proc)) (length args))
                                (apply-proc
                                    (update-proc-env name env proc)
                                    (eval-operands args env return break continue)
                                    return break continue
                                )
                                (error
                                    "CALL: Mismatched parameters and arguments:" name (proc-params proc)
                                    'expected (length (proc-params proc)) 'got (length args)
                                )
                            )
                        )
                        (get-var name env)
                    )
                    (error "CALL: Unknown method:" name)
                )
            )
            (method-name exp)
            (method-args exp)
        )
    ))
))

; ================================

