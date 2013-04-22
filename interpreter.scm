; ================================
; Author: Sean Fox (saf66)
; To run: (interpret "filename" "Class")
; Notes:
;     I'm using DrRacket with #lang set to R5RS.
;     Both implicit parent-class function calls and recursion are broken.
; ================================

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

(load "classParser.scm")

(define interpret (lambda (file class)
    (call/cc (lambda (return)
        (eval-exp
            (append (parser file) (list
               (list 'return (list 'funcall (list 'dot (string->symbol class) 'main)))
            ))
            the-global-env
            (make-class (string->symbol class) (list) (list) (list))
            (list)
            return
            (lambda () (error "BREAK: Break called outside a loop!"))
            (lambda () (error "CONTINUE: Continue called outside a loop!"))
        )
    ))
))

; ================================
;[todo] Uncategorized Functions






















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
(define var-define? (lambda (exp)
    (or
        (tagged-list? exp 'var)
        (tagged-list? exp 'static-var)
    )
))
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

(define eval-operands (lambda (ops env class this return break continue)
    (map (lambda (exp) (eval-exp exp env class this return break continue)) ops)
))
(define eval-statement (lambda (exp env class this return break continue)
    (apply-proc
        (eval-exp (operator exp) env class this return break continue)
        (eval-operands (operands exp) env class this return break continue)
        class this return break continue
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

(define eval-seq (lambda (seq env class this return break continue)
    (cond
        ((last-exp? seq) (eval-exp (first-exp seq) env class this return break continue))
        (else
            (eval-exp (first-exp seq) env class this return break continue)
            (eval-seq (rest-exps seq) env class this return break continue)
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

(define update-proc-env (lambda (vars env proc)
    (make-proc
        (proc-params proc)
        (proc-body proc)
        (copy-vars! vars env (new-frame (proc-env proc)))
    )
))

(define apply-proc (lambda (proc args class this return break continue)
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
                class this return break continue
            )
        )
        ((method-define? proc)
            (eval-seq
                (method-body proc)
                (extend-env
                    (method-params proc)
                    args
                    (method-env proc)
                )
                class this return break continue
            )
        )
        (else (error "APPLY: Unknown procedure:" proc))
    )
))

; ================================
; Expression

(define eval-exp (lambda (exp env class this return break continue)
    (cond
        ((self-eval? exp) exp)
        ((var? exp) (eval-var-lookup exp env class this return break continue))
        ((var-define? exp) (eval-var-define exp env class this return break continue))
        ((var-assign? exp) (eval-var-assign exp env class this return break continue))
        ((return? exp) (eval-return exp env class this return break continue))
        ((break? exp) (break))
        ((continue? exp) (continue))
        ((block? exp) (eval-block exp env class this return break continue))
        ((conditional? exp) (eval-conditional exp env class this return break continue))
        ((while? exp) (eval-while exp env class this return break continue))
        ((method-define? exp) (eval-method-define exp env class this return break continue))
        ((method-call? exp) (eval-method-call exp env class this return break continue))
        ((class-define? exp) (eval-class-define exp env class this return break continue))
        ((dot? exp) (eval-dot exp env class this return break continue))
        ((sequence? exp) (eval-seq exp env class this return break continue))
        ((statement? exp) (eval-statement exp env class this return break continue))
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

(define eval-var-lookup (lambda (exp env class this return break continue)
    (display (class-extend class))
    (newline)
    (if (var-exist? exp env)
        (get-var exp env)
        (if (null? (class-extend class))
            (error "GET: Unbound variable:" exp)
            (
                (lambda (super)
                    (
                        (lambda (super-env)
                            (display (class-body super))
                            (newline)
                            (eval-exp (class-body super) super-env super this return break continue)
                            (eval-var-lookup exp super-env super this return break continue)
                        )
                        (new-frame (class-env super))
                    )
                )
                (eval-exp (cadr (class-extend class)) env class this return break continue)
            )
        )
    )
))

(define eval-var-define (lambda (exp env class this return break continue)
    (
        (lambda (val)
            (new-var! (definition-var exp) val env)
            val
        )
        (eval-exp (definition-val exp) env class this return break continue)
    )
))

(define eval-var-assign (lambda (exp env class this return break continue)
    (
        (lambda (val)
            (set-var! (assignment-var exp) val env)
            val
        )
        (eval-exp (assignment-val exp) env class this return break continue)
    )
))

; ================================
; Return

(define return? (lambda (exp) (tagged-list? exp 'return)))
(define return-val (lambda (exp) (cadr exp)))

(define eval-return (lambda (exp env class this return break continue)
    (return (eval-exp (return-val exp) env class this return break continue))
))

; ================================
; Control Flow

(define break? (lambda (exp) (tagged-list? exp 'break)))
(define continue? (lambda (exp) (tagged-list? exp 'continue)))

; ================================
; Block

(define block? (lambda (exp) (tagged-list? exp 'begin)))
(define block-inner (lambda (exp) (cdr exp)))

(define eval-block (lambda (exp env class this return break continue)
    (eval-exp (block-inner exp) (new-frame env) class this return break continue)
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

(define eval-conditional (lambda (exp env class this return break continue)
    (if (true? (eval-exp (conditional-predicate exp) env class this return break continue))
        (eval-exp (conditional-consequent exp) (new-frame env) class this return break continue)
        (eval-exp (conditional-alternative exp) (new-frame env) class this return break continue)
    )
))

; ================================
; While Loop

(define while? (lambda (exp) (tagged-list? exp 'while)))
(define while-condition (lambda (exp) (cadr exp)))
(define while-body (lambda (exp) (caddr exp)))

(define eval-while (lambda (exp env class this return break continue)
    (define eval-while-inner (lambda (exp env class this return break continue)
        (cond
            ((true? (eval-exp (while-condition exp) env class this return break continue))
                (call/cc (lambda (continue)
                    (eval-exp (while-body exp) env class this return break continue)
                ))
                (eval-while-inner exp env class this return break continue)
            )
            (else 'nop)
        )
    ))
    (call/cc (lambda (break)
        (eval-while-inner exp (new-frame env) class this return break continue)
    ))
))

; ================================
; Method Definition

(define make-method (lambda (name params body env) (list 'function name params body env)))
(define method-define? (lambda (exp)
    (or
        (tagged-list? exp 'function)
        (tagged-list? exp 'static-function)
    )
))
(define method-name (lambda (exp) (cadr exp)))
(define method-params (lambda (exp) (caddr exp)))
(define method-body (lambda (exp) (cadddr exp)))
(define method-env (lambda (exp) (cadddr (cdr exp))))

(define eval-method-define (lambda (exp env class this return break continue)
    (
        (lambda (name params body)
            (new-var! name (make-method name params body env) env)
        )
        (method-name exp)
        (method-params exp)
        (method-body exp)
    )
))

; ================================
; Method Call

(define method-call? (lambda (exp) (tagged-list? exp 'funcall)))
(define method-args (lambda (exp) (cddr exp)))

(define class-of (lambda (var env class this return break continue)
    (
        (lambda (class var)
            (display (class-name class))
            (newline)
            (if (var-exist? var env)
                class
                (if (null? (class-extend class))
                    (error "CLASS: Unbound variable:" var)
                    (
                        (lambda (super)
                            (
                                (lambda (super-env)
                                    (eval-exp (class-body super) super-env super this return break continue)
                                    (class-of var super-env super this return break continue)
                                )
                                (new-frame (class-env super))
                            )
                        )
                        (eval-exp (cadr (class-extend class)) env class this return break continue)
                    )
                )
            )
        )
        (if (dot? var)
            (eval-exp (dot-left var) env class this return break continue)
            class
        )
        (if (dot? var)
            (dot-right var)
            var
        )
    )
))

(define eval-method-call (lambda (exp env class this return break continue)
    (display exp)
    (newline)
    (call/cc (lambda (return)
        (
            (lambda (name args method)
                (
                    (lambda (params proc)
                        (if (= (length params) (length args))
                            (apply-proc
                                (if (dot? name)
                                    proc
                                    ;(make-proc
                                    ;    (proc-params proc)
                                    ;    (proc-body proc)
                                    ;    (
                                    ;        (lambda (new-env)
                                    ;            (new-var! name (eval-var-lookup name env class this return break continue) new-env)
                                    ;            new-env
                                    ;        )
                                    ;        (new-frame (proc-env proc))
                                    ;    )
                                    ;)
                                    (update-proc-env (list name) env proc)
                                )
                                (eval-operands args env class this return break continue)
                                (class-of name env class this return break continue)
                                this return break continue
                            )
                            (error
                                "CALL: Mismatched parameters and arguments:" name params
                                'expected (length params) 'got (length args)
                            )
                        )
                    )
                    (method-params method)
                    (make-proc (method-params method) (method-body method) (method-env method))
                )
            )
            (method-name exp)
            (method-args exp)
            (eval-exp (method-name exp) env class this return break continue)
        )
    ))
))

; ================================
; Class Definition

(define make-class (lambda (name extend body env) (list 'class name extend body env)))
(define class-define? (lambda (exp) (tagged-list? exp 'class)))
(define class-name (lambda (exp) (cadr exp)))
(define class-extend (lambda (exp) (caddr exp)))
(define class-body (lambda (exp) (cadddr exp)))
(define class-env (lambda (exp) (cadddr (cdr exp))))

(define eval-class-define (lambda (exp env class this return break continue)
    (
        (lambda (name extend body)
            (new-var! name (make-class name extend body env) env)
        )
        (class-name exp)
        (class-extend exp)
        (class-body exp)
    )
))

; ================================
; Dot Expression

(define make-dot (lambda (left right) (list 'dot left right)))
(define dot? (lambda (dot) (tagged-list? dot 'dot)))
(define dot-left (lambda (dot) (cadr dot)))
(define dot-right (lambda (dot) (caddr dot)))

(define eval-dot (lambda (exp env class this return break continue)
    (display exp)
    (newline)
    (
        (lambda (object target)
            (
                (lambda (extend object-env)
                    (if (null? extend)
                        'nop
                        'nop
                    )
                    (eval-exp (class-body object) object-env object this return break continue)
                    (eval-exp target object-env object this return break continue)
                )
                (class-extend object)
                (new-frame (class-env object))
            )
        )
        (cond
            ((eq? 'super (dot-left exp))
                (
                    (lambda (class)
                        (display (class-name class))
                        (newline)
                        (eval-exp (cadr (class-extend class)) env class this return break continue)
                    )
                    (if (null? (class-body class))
                        (eval-exp (class-name class) env class this return break continue)
                        class
                    )
                )
            )
            (else (eval-exp (dot-left exp) env class this return break continue))
        )
        (dot-right exp)
    )
))

; ================================
;



; ================================
;



; ================================
;



; ================================
;



; ================================
;

























; ================================

(display (parser "test.txt"))
(newline)
(display (interpret "test.txt" "Square"))