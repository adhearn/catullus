(library (catullus languages)
  (export L0 unparse-L0
          L1 unparse-L1
          L1.5 unparse-L1.5
          L2 unparse-L2
          L3 unparse-L3
          L4 unparse-L4
          L5 unparse-L5
          L6 unparse-L6
          L7 unparse-L7
          L8 unparse-L8
          L9 unparse-L9
          L10 unparse-L10
          L11 unparse-L11
          L12 unparse-L12
          L13 unparse-L13
          L14 unparse-L14
          L100 unparse-L100)
  (import (rnrs) (nanopass) (catullus helpers))

  (define-language L0
    (terminals
     (variable (v))
     (constant (c))
     (primitive (pr))
     (datum (d)))
    (Expr (e expr)
          v
          c
          pr
          (quote d)
          (let ((v* e*) ...) expr1 ... expr2)
          (letrec ((v* e*) ...) expr1 ... expr2)
          (lambda (v* ...) expr1 ... expr2)
          (if e1 e2 e3)
          (if e1 e2)
          (begin e0 ... e1)
          (set! v e)
          (e0 e1 ...)))

  (define-language L1
    (extends L0)
    (Expr (e expr)
          (- (let ((v* e*) ...) expr1 ... expr2)
             (letrec ((v* e*) ...) expr1 ... expr2)
             (lambda (v* ...) expr1 ... expr2))
          (+ (let ((v* e*) ...) expr)
             (letrec ((v* e*) ...) expr)
             (lambda (v* ...) expr))))

  ;; Introduces the primcall form
  ;; This is required much later, in normalize-context, but it's convenient to do it now.
  (define-language L1.5
    (extends L1)
    (Expr (e expr)
      (- pr)
      (+ (primcall pr e* ...))))

  (define-language L2
    (extends L1.5)
    (terminals
      (- (datum (d))))
    (Expr (e expr)
      (- (quote d)
         c)
      (+ (quote c)))
    )

  ; The language after we've identified assigned variables.
  (define-language L3
    (extends L2)
    ; Adding the a makes it much easier to write passes that deal with both a
    ; list of bound variables and a list of assigned variables
    ; (e.g. the letrec case in purify-letrec).
    (terminals
      (- (variable (v)))
      (+ (variable (v a x))))
    (AssignedBody (abody)
       (+ (assigned (a* ...) expr)))
    (Expr (e expr)
          (- (let ((v* e*) ...) expr)
             (letrec ((v* e*) ...) expr)
             (lambda (v* ...) expr))
          (+ (let ((v* e*) ...) abody)
             (letrec ((v* e*) ...) abody)
             (lambda (v* ...) abody))))

  (define-language L4
    (extends L3)
    (LambdaBody (lbody)
      (+ (lambda (v* ...) abody)))
    (Expr (e expr)
      (- (letrec ((v* e*) ...) abody)
         (lambda (v* ...) abody))
      (+ (letrec ((v* lbody) ...) expr)
         lbody)))

    ; Language after we've finished assignment conversion.
    ; Get rid of the AssignedBody nonterminal
    (define-language L5
      (extends L4)
      (AssignedBody (abody)
        (- (assigned (a* ...) expr)))
      (Expr (e expr)
        (- (let ((v* e*) ...) abody))
        (+ (let ((v* e*) ...) expr)))
      (LambdaBody (lbody)
        (- (lambda (v* ...) abody))
        (+ (lambda (v* ...) expr))))

    (define-language L6
      (extends L5)
      (Expr (e expr)
        (- lbody)))

    (define-language L7
      (extends L6)
      (FreeBody (f-body)
        (+ (free (v* ...) expr)))
      (LambdaBody (lbody)
        (- (lambda (v* ...) expr))
        (+ (lambda (v* ...) f-body))))

    (define-language L8
      (extends L7)
      (terminals
        (+ (label (l))))
      (Expr (e expr)
        (- (letrec ([v* lbody] ...) expr))
        (+ (letrec ([l* lbody] ...) closure)))
      (Closure (closure)
        (+ (closures ((v l v* ...) ...) expr)))
      (BindFree (bf)
        (+ (bind-free (v1 v* ...) expr)))
      (FreeBody (f-body)
        (- (free (v* ...) expr)))
      (LambdaBody (lbody)
        (- (lambda (v* ...) f-body))
        (+ (lambda (v* ...) bf)))
      )

    ;; Output of introduce-procedure-primitives.
    ;; We've removed the closures special form within letrecs and the bind-free form in
    ;; lambdas. Instead, we will explicitly make procedures with calls to (make-procedure) and
    ;; accessing free variables within procedures via (procedure-ref)
    (define-language L9
      (extends L8)
      (Expr (e expr)
        (- (letrec ([l* lbody] ...) closure))
        (+ (letrec ([l* lbody] ...) expr)))
      (LambdaBody (lbody)
        (- (lambda (v* ...) bf))
        (+ (lambda (v* ...) expr)))
      (BindFree (bf)
        (- (bind-free (v1 v* ...) expr)))
      (Closure (closure)
        (- (closures ((v l v* ...) ...) expr))))

    (define-language L10
      (extends L9)
      (entry Program)
      (Program (prog)
        (+ (letrec ([l* lbody] ...) expr)))
      (Expr (e expr)
        (- (letrec ([l* lbody] ...) expr))))

    ;; Output of normalize-context
    ;; This language is so different from the previous language that it doesn't
    ;; make sense to define it as an extension language.
    (define-language L11
      (entry Program)
      (terminals
        (label (l))
        (variable (x))
        (constant (c))
        (effect-primitive (effect-prim))
        (predicate-primitive (pred-prim))
        (value-primitive (value-prim)))
      (Program (prog)
        (letrec ([l* lbody] ...) body))
      (LambdaBody (lbody)
        (lambda (x* ...) body))
      (Effect (e)
        (nop)
        (if p e1 e2)
        (begin e* ... e)
        (let ([x* v*] ...) e)
        (primcall effect-prim v* ...)
        (v v* ...))
      (Predicate (p)
        (false)
        (true)
        (if p1 p2 p3)
        (begin e* ... p)
        (let ([x* v*] ...) p)
        (primcall pred-prim v* ...)
        (v v* ...))
      (Value (v body)
        l
        x
        (quote c)
        (if p v1 v2)
        (begin e* ... v)
        (let ([x* v*] ...) v)
        (primcall value-prim v* ...)
        (v v* ...)))

    (define-language L12
      (extends L11)
      (terminals
       (+ (integer (i offset))))
      (Value (v body)
;        (- (quote c))
        (+ (alloc i)
           (mref i)))
      (Effect (e)
        (+ (mset! v0 offset v1)))

      )

    ;; Output of remove-let. let statements are replaced by set!
    (define-language L13
      (extends L12)
      (Effect (e)
        (- (let ([x* v*] ...) e))
        (+ (set! x v)))
      (Predicate (p)
        (- (let ([x* v*] ...) p)))
      (Value (v body)
        (- (let ([x* v*] ...) v))))

        ;; Output of remove-complex-opera*. The arguments to primcalls must be trivs.
    ;; Similarly, in the (rator rand* ...) form, rator and rand* must be trivs.
    (define-language L14
      (extends L13)
      (Triv (triv)
        (+ (quote c)
           i
           l
           x ))
      (Value (v body)
        (- (v v* ...)
           (primcall value-prim v* ...))
        (+ (triv triv* ...)
           (primcall value-prim triv* ...)))
      (Predicate (p)
        (- (v v* ...)
           (primcall pred-prim v* ...))
        (+ (triv triv* ...)
           (primcall pred-prim triv* ...)))
      (Effect (e)
        (- (v v* ...)
           (primcall effect-prim v* ...))
        (+ (triv triv* ...)
           (primcall effect-prim triv* ...))))

    ;; Output of flatten-set!. We now restrict what can occur as the RHS of a set!
    (define-language L100
      (extends L14)
      (Rhs (rhs)
        (+ triv
           (primcall value-prim triv* ...)
           (alloc i)
           (mref i)
           (triv triv* ...)))
      (Effect (e)
        (- (set! x v))
        (+ (set! x rhs)))
      (Value (v body)
        (+ rhs)
        (- (primcall value-prim triv* ...)
           (quote c)
           (alloc i)
           (mref i)
           (triv triv* ...)
           l x))
      )

)
