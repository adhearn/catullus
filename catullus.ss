(library (catullus)
  (export remove-implicit-begin
          introduce-primcall
          convert-complex-datum
          uncover-assigned
          purify-letrec
          convert-assignments
          remove-anonymous-lambda
          catullus-compile)
  (import (rnrs) (nanopass) (catullus helpers) (catullus languages) (only (chezscheme) gensym printf pretty-print format system))

  (define test-fun
    (lambda ()
      (display "test")
      (newline)))



  (define make-tmp
    (lambda ()
      (unique-name 'tmp)))

  (define make-var
    (lambda (prefix)
      (unique-name prefix)))

  ; Parses an S-expression representing the input to the compiler, which handles
  ; a subset of legal Scheme. Also does alpha renaming, and a bit of convenience
  ; work to make the language a bit more regular (for example, quoting #t and #f),
  ; parsing and, or, and not, etc.).
  ;
  ; Possible inputs => outputs are:
  ; 1. a pair => keyword, primitive, application
  ; 2. a symbol => a variable or a primitive
  ; 3. a constant => a constant
  ;
  ; Despite the fact that even my class compiler checked the arity of arguments to
  ; primitives, I'm not doing so here. I have no good reason for it, I'm just lazy.
  ;
  ; This pass really ought to be reworked quite a bit. I'm rushing it for now because
  ; I really want to test the other passes I've written.
  (define-pass parse-scheme : * (e) -> L0 ()
    (definitions
      (define keyword?
        (lambda (k)
          (member k '(let letrec lambda quote if begin and or not set!))))
      (define make-uvar
        (lambda ()
          (gensym "u")))
      (with-output-language (L0 Expr)
        (define Expr*
          (lambda (expr* env)
            (map (lambda (expr) (Expr expr env)) expr*)))
        ; Helper that takes a list of Exprs, applies Expr to them, then returns a list of all but the last expr
        ; and the last expr separately, so that we can correctly generate the correct 'shape'
        ; for let, letrec, lambda, and begin
        (define Expr*-body
          (lambda (e* env)
            (let loop ([processed-reversed '()]
                       [unprocessed e*])
              ;(printf "Expr*-body | processed-reversed: ~s ;;; unprocessed: ~s\n" processed-reversed unprocessed)
              (if (null? unprocessed)
                  (values (reverse (cdr processed-reversed)) (car processed-reversed))
                  (loop (cons (Expr (car unprocessed) env) processed-reversed) (cdr unprocessed))))))
        ; This is going to give really terrible error messages for malformed lets and letrecs
        (define Keyword
          (lambda (expr env)
            (case (car expr)
              [(letrec) (let* ([var* (map car (cadr expr))]
                               [bound-expr* (map cadr (cadr expr))]
                               [body-expr* (cddr expr)]
                               [uvar* (map (lambda (x) (make-uvar)) var*)]
                               [extended-env (append (map cons var* uvar*) env)]
                               [processed-bound-expr* (Expr* bound-expr* extended-env)])
                          (let-values ([(expr*-body expr-body) (Expr*-body body-expr* extended-env)])
                            `(letrec ([,uvar* ,processed-bound-expr*] ...) ,expr*-body ... ,expr-body)))]
              [(let) (let* ([var* (map car (cadr expr))]
                               [bound-expr* (map cadr (cadr expr))]
                               [body-expr* (cddr expr)]
                               [uvar* (map (lambda (x) (make-uvar)) var*)]
                               [extended-env (append (map cons var* uvar*) env)]
                               [processed-bound-expr* (Expr* bound-expr* extended-env)])
                       (let-values ([(expr*-body expr-body) (Expr*-body body-expr* extended-env)])
                         `(let ([,uvar* ,processed-bound-expr*] ...) ,expr*-body ... ,expr-body)))]
              [(lambda) (let* ([var* (cadr expr)]
                               [body-expr* (cddr expr)]
                               [uvar* (map (lambda (x) (make-uvar)) var*)]
                               [extended-env (append (map cons var* uvar*) env)])
                          (let-values ([(expr*-body expr-body) (Expr*-body body-expr* extended-env)])
                            `(lambda (,uvar* ...) ,expr*-body ... ,expr-body)))]
              [(quote) (if (or (datum? (cadr expr))
                               (variable? (cadr expr)))
                           `(quote ,(cadr expr))
                           (error 'parse-scheme "Malformed quote expression: ~s" expr))]
              [(if) (cond
                     [(= (length expr) 4) (let ([test (Expr (cadr expr) env)]
                                                [conseq (Expr (caddr expr) env)]
                                                [alt (Expr (cadddr expr) env)])
                                            `(if ,test ,conseq ,alt))]
                     [(= (length expr) 3) (let ([test (Expr (cadr expr) env)]
                                                [conseq (Expr (caddr expr) env)])
                                            `(if ,test ,conseq))]
                     [else (error 'parse-scheme "Malformed if expression: ~s" expr)])]
              [(begin) (let ([body* (cdr expr)])
                         ; we only have one expression in the body, so return that instead of a begin form
                         (if (= (length body*) 1)
                             (Expr (car body*) env)
                             (let-values ([(expr*-body expr-body) (Expr*-body body* env)])
                               `(begin ,expr*-body ... ,expr-body))))]
              [(set!) (let ([var (cadr expr)]
                            [e (caddr expr)])
                        (if (symbol? var)
                            (let ([p (assq var env)])
                              (if p
                                  `(set! ,(cdr p) ,(Expr e env))
                                  (error 'parse-scheme "Malformed set! (attempted to set! unbound variable) ~s" expr)))))]
              [(and) `(and ,(Expr* (cdr expr) env) ...)]
              [(or) `(or ,(Expr* (cdr expr) env) ...)]
              [(not) `(not ,(Expr (cadr expr) env))])))
        (define Primitive
          (lambda (prim args env)
            `(,prim ,(Expr* args env) ...)))
        (define App
          (lambda (rator rand* env)
            `(,(Expr rator env) ,(Expr* rand* env) ...)))))
    (Expr : * (e env) -> Expr ()
      (cond
       [(pair? e) (cond
                   [(and (keyword? (car e)) (not (assq (car e) env))) (Keyword e env)]
                   [(and (primitive? (car e)) (not (assq (car e) env))) (Primitive (car e) (cdr e) env)]
                   [else (App (car e) (cdr e) env)])]
       [(symbol? e) (let ([p (assq e env)])
                      (cond
                       [p (cdr p)]
                       [(primitive? e) e]
                       [else (error 'parse-scheme "Unbound variable ~s" e)]))]
       [(constant? e) e]
       [else (error 'parse-scheme "Invalid expression ~s" e)]))
    (Expr e '()))
                          

  ; It's convenient to assume that lambda, let, and letrec all only have a single expression as their body. Might as well do this pass at the beginning.
  (define-pass remove-implicit-begin : L0 (e) -> L1 ()
    (Expr : Expr (e) -> Expr ()
          [(let ((,v ,[e])...) ,[expr1] ... ,[expr2])
           (if (null? expr1)
               `(let ((,v ,e) ...) ,expr2)
               `(let ((,v ,e) ...) (begin ,expr1 ... ,expr2)))]
          [(letrec ((,v ,[e])...) ,[expr1] ... ,[expr2])
           (if (null? expr1)
               `(letrec ((,v ,e) ...) ,expr2)
               `(letrec ((,v ,e) ...) (begin ,expr1 ... ,expr2)))]
          [(lambda (,v ...) ,[expr1] ... ,[expr2])
           (if (null? expr1)
               `(lambda (,v ...) ,expr2)
               `(lambda (,v ...) (begin ,expr1 ... ,expr2)))]))


  (define-pass introduce-primcall : L1 (e) -> L1.5 ()
    (Expr : Expr (e) -> Expr ()
      [(,pr ,[e*] ...) `(primcall ,pr ,e* ...)]
      [,pr
       (let* ([p (assq pr primitives)]
              [num-args (if p
                            (cdr p)
                            (error 'introduce-primcall "Unexpected primitive ~s" pr))]
              [args (simple-dotimes num-args make-tmp)])
         `(lambda ,num-args (primcall ,pr ,args ...)))]))

  (define-pass convert-complex-datum : L1.5 (e) -> L2 ()
    ; In the model compiler, I used multiple return values. Using set! is ridiculously cleaner.
    ; We also quote constants in this pass.
    (definitions
      (define tmp* '())
      (define complex-data* '()))
    (Expr : Expr (e) -> Expr ()
      (definitions
        (define datum-helper
          (lambda (datum)
            (cond
             [(constant? datum) `(quote ,datum)]
             [(variable? datum) `(quote ,datum)]
             [(pair? datum)
              `(primcall cons ,(datum-helper (car datum)) ,(datum-helper (cdr datum)))]))))
      [(quote ,d) (if (constant? d)
                      `(quote ,d)
                      (let ([tmp (make-tmp)]
                            [datum (datum-helper d)])
                        (set! tmp* (cons tmp tmp*))
                        (set! complex-data* (cons datum complex-data*))
                        tmp))]
      [,c `(quote ,c)])
    ; Call the transformer directly, then decide if we need to wrap it in a let or not.
    (let ([e (Expr e)])
      (if (null? tmp*)
          e
          `(let ([,tmp* ,complex-data*] ...) ,e))))

  ; Determine which variables are assigned. We will use this information in a later
  ; pass to turn them into cons cells ("poor man's boxes")
  (define-pass uncover-assigned : L2 (e) -> L3 ()
    (Expr : Expr (e) -> Expr ('())
      [(letrec ([,v* ,[e* assigned**]] ...) ,[expr assigned*])
       (let ([assigned (intersection v* (union (apply union assigned**) assigned*))])
         (values `(letrec ([,v* ,e*] ...) (assigned (,assigned ...) ,expr))
                 (difference (union assigned* (apply union assigned**)) v*)))]
      [(let ([,v* ,[e* assigned**]] ...) ,[expr assigned*])
       (let ([assigned (intersection v* (union (apply union assigned**) assigned*))])
         (values `(let ([,v* ,e*] ...) (assigned (,assigned ...) ,expr))
                 (difference (union assigned assigned*) v*)))]
      [(lambda (,v* ...) ,[expr assigned])
       (values `(lambda (,v* ...) (assigned (,(intersection assigned v*) ...) ,expr))
               (difference assigned v*))]
      [(set! ,v ,[expr assigned])
       (values `(set! ,v ,expr) (union (list v) assigned))]
      [(if ,[expr1 assigned1] ,[expr2 assigned2] ,[expr3 assigned3])
       (values `(if ,expr1 ,expr2 ,expr3)
               (union assigned1 assigned2 assigned3))]
      [(begin ,[e* assigned**] ... ,[e assigned*])
       (values `(begin ,e* ... ,e)
               (union assigned* (apply union assigned**)))]
      [(quote ,c) (values `(quote ,c) '())]
      [(,[e0 assigned*] ,[e1 assigned**] ...)
       (values `(,e0 ,e1 ...)
               (union assigned* (apply union assigned**)))])
    (let-values ([(expr assigned) (Expr e)])
      (if (not (null? assigned))
          (error 'uncover-assigned "Unbound but set! variables: " assigned)
          expr)))

  ; We want only lambdas to occur on the RHS of letrec forms. (This is definitely a requirement
  ; if I want to CPS at some point in the future. The class compiler uses an algorithm that
  ; partitions letrec bindings into 3 groups: simple, lambda, and complex. According to Andy Keep,
  ; another algorithm is provided in "Fixing Letrec (reloaded)", at least for r6rs semantics. That
  ; paper uses Tarjan's algorithm, which we'll use later when optimizing the representation of closures.
  ; For now, I'm sticking to the class compiler version, with a note that I really should look into
  ; the method from "Fixing Letrec (reloaded)", especially since I'm not sure my algorithm actually
  ; correctly identifies simple things (it doesn't pay attention to the possibility that builtin functions
  ; might fail to terminate).
  (define-pass purify-letrec : L3 (e) -> L4 ()
    (definitions
      (define categorize-binding
        (lambda (x expr assigned*)
          ;(printf "***categorize-binding*** ")
          (if (member x assigned*)
              (begin ;(printf "~s: COMPLEX\n" expr)
                     'complex)
              ;We've already processed expr, so we match against L4 expr, NOT L3
              (nanopass-case (L4 Expr) expr
                [(lambda (,v* ...) ,abody)
                 ;(printf "~s: LAMBDA\n" expr)
                 'lambda]
                [else ;(printf "~s: SIMPLE\n" expr)
                 'simple])))))
    (Expr : Expr (e) -> Expr ()
      (definitions
        ; We have to be a bit more careful than I was with the class compiler. The nanopass framework
        ; will require us to keep our vars and exprs separate until we're actually ready to build the output
        ; language. This function is also really poorly written. I've copied it almost verbatim from my
        ; class compiler, but it can definitely be better. At the very least, I probably don't need to pass
        ; around 7 variables each time I loop.
        (define categorize-binding*
          (lambda (var* expr* assigned*)
            (let loop ([var* var*] [expr* expr*]
                       [simple-var* '()] [simple-expr* '()]
                       [lambda-var* '()] [lambda-expr* '()]
                       [complex-var* '()] [complex-expr* '()])
              (cond
               [(null? var*) (values (reverse simple-var*) (reverse simple-expr*)
                                     (reverse lambda-var*) (reverse lambda-expr*)
                                     (reverse complex-var*) (reverse complex-expr*))]
               [else (let ([var (car var*)]
                           [expr (car expr*)])
                       (let ([category (categorize-binding var expr assigned*)])
                         (case category
                           [(simple) (loop (cdr var*) (cdr expr*)
                                           (cons var simple-var*) (cons expr simple-expr*)
                                           lambda-var* lambda-expr*
                                           complex-var* complex-expr*)]
                           [(lambda) (loop (cdr var*) (cdr expr*)
                                           simple-var* simple-expr*
                                           (cons var lambda-var*) (cons expr lambda-expr*)
                                           complex-var* complex-expr*)]
                           [(complex) (loop (cdr var*) (cdr expr*)
                                           simple-var* simple-expr*
                                           lambda-var* lambda-expr*
                                           (cons var complex-var*) (cons expr complex-expr*))])))]))))
        ; This is pretty much taken directly from Andy's scheme-to-c compiler, since it's a lot better than the
        ; shitty stuff I had for the class compiler. Since I want to implement Fixing Letrec (reloaded) pretty
        ; soon anyway, I feel not too horrible about taking it from him. (He and Prof. Dybvig taught me everything
        ; I know about compilers anyway :))
        (define build-begin
          (lambda (v* e* body)
            (let ([e* (map (lambda (v e) `(set! ,v ,e)) v* e*)])
              (nanopass-case (L3 Expr) body
                             [(begin ,expr* ... ,expr) `(begin ,(append e* expr*) ... ,expr)]
                             [else `(begin ,e* ... ,body)])))))
      [(letrec ([,v* ,[e*]] ...) (assigned (,a* ...) ,[expr]))
       (cond
        [(null? v*) `(letrec () ,expr)]
        [else (let-values ([(simple-var* simple-expr* lambda-var* lambda-expr* complex-var* complex-expr*) (categorize-binding* v* e* a*)])
                (cond
                 [(null? complex-var*)
                  (cond
                   [(null? lambda-var*) `(let ([,simple-var* ,simple-expr*] ...) (assigned () ,expr))]
                   [(null? simple-var*) `(letrec ([,lambda-var* ,lambda-expr*] ...) ,expr)]
                   [else `(let ([,simple-var* ,simple-expr*] ...) (assigned () (letrec ([,lambda-var* ,lambda-expr*] ...) ,expr)))])]
                 [else
                  `(let ([,simple-var* ,simple-expr*] ...)
                     (assigned ()
                       (let ([,complex-var* ,(map (lambda (x) `(quote #f)) complex-var*)] ...)
                         (assigned (,complex-var* ...)
                           (letrec ([,lambda-var* ,lambda-expr*] ...)
                             ,(build-begin complex-var* complex-expr* expr))))))]))])]))

  ; Instead of setting variables, we create temp variable, which is initialized #f.
  ; Instead of using boxes, we use cons cells. This is a bit inefficient, since it
  ; requires an extra word, but we already need to support cons anyway, so it's
  ; less work from an implementation standpoint.
  ; 
  (define-pass convert-assignments : L4 (e) -> L5 ()
    (definitions
      ; Andy's build-let method is much cleaner than my class compiler method
      ; (which I don't think would work in the nanopass framework anyway,
      ; since things won't be the right shape).
      (define env-lookup
        (lambda (x env)
          (let ([p (assq x env)])
            (if p
                (cdr p)
                x))))
      (with-output-language (L5 Expr)
        (define build-let
          (lambda (x* e* expr)
            (if (null? x*)
                expr
                `(let ([,x* ,e*] ...) ,expr))))))
    (Expr : Expr (e [env '()]) -> Expr ()
      [(let ([,v* ,[expr*]] ...) (assigned (,a* ...) ,expr))
       (let* ([temp-var* (map (lambda (a) (make-tmp)) a*)]
              [temp-alist (map cons a* temp-var*)]
              [unassigned (difference v* a*)]
              [env (append temp-alist env)])
         (build-let (map (lambda (x) (env-lookup x env)) v*)
                    expr*
                    (build-let a*
                               (map (lambda (x) `(primcall cons ,x (void))) temp-var*)
                               (Expr expr env))))]
      [(set! ,v ,[e]) `(set-car! ,v ,e)]
      [,v (if (assq v env) `(car ,v) v)])
    (LambdaBody : LambdaBody (lb env) -> LambdaBody ()
      [(lambda (,v* ...) (assigned (,a* ...) ,expr))
       (let* ([temp-var* (map (lambda (x) (make-tmp)) a*)]
              [env (append (map cons a* temp-var*) env)]
              [expr (Expr expr env)])
         (if (null? a*)
             `(lambda (,v* ...) ,expr)
             `(lambda (,(map (lambda (x) (env-lookup x env)) v*) ...)
                ,(build-let a* (map (lambda (x t) `(,x (cons ,t (void)))) a* temp-var*) expr))))]))

  (define-pass remove-anonymous-lambda : L5 (e) -> L6 ()
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,v* (lambda (,v2* ...) ,[expr])] ...) ,[e])
       `(letrec ([,v* (lambda (,v2* ...) ,expr)] ...) ,e)])
    (LambdaBody : LambdaBody (lb) -> Expr ()
      [(lambda (,v* ...) ,[expr])
       (let ([anon (make-var "anon")])
         `(letrec ([,anon (lambda (,v* ...) ,expr)])
            ,anon))]))

  (define-pass emit-L6 : L6 (e) -> * ()
    (definitions
      (define emit-var
        (lambda (v)
          (printf "~s" v)))
      (define emit-letrec-binding
        (lambda (v lbody)
          (printf "(")
          (emit-var v)
          (printf " ")
          (LambdaBody lbody)
          (printf ")")))
      (define emit-let-binding
        (lambda (v e)
          (printf "(")
          (emit-var v)
          (printf " ")
          (Expr e)
          (printf ")"))))
    (Expr : Expr (e) -> * ()
      [(letrec ([,v* ,lbody*] ...) ,expr) (printf "(letrec (")
                                          (for-each emit-letrec-binding v* lbody*)
                                          (printf ") ")
                                          (Expr expr)
                                          (printf ")")]
      [(let ([,v* ,e*] ...) ,expr) (printf "(let (")
                                   (for-each emit-let-binding v* e*)
                                   (printf ") ")
                                   (Expr expr)
                                   (printf ")")]
      [(if ,e1 ,e2 ,e3) (printf "(if ") (Expr e1) (printf " ") (Expr e2) (printf " ") (Expr e3) (printf ")")]
      [(if ,e1 ,e2) (printf "(if ") (Expr e1) (printf " ") (Expr e2) (printf ")")]
      [(begin ,e0* ... ,e1) (printf "(begin ") (for-each (lambda (e) (Expr e) (printf " ")) e0*) (Expr e1) (printf ")")]
      [(set! ,v ,e) (printf "set! ") (emit-var v) (printf " ") (Expr e) (printf ")")]
      [(quote ,c) (printf "(quote ") (printf "~s" c) (printf ")")]
      [(primcall ,pr ,e* ...)
       (printf "(~s " pr)
       (for-each (lambda (e) (Expr e) (printf " ")) e*)
       (printf ")")
      ]
      [(,e0 ,e1* ...) (printf "(") (Expr e0) (for-each (lambda (e) (printf " ") (Expr e)) e1*) (printf ")")]
      [,v (emit-var v)]
;      [,c (printf "~s" c)]
      )
    (LambdaBody : LambdaBody (lb) -> * ()
      [(lambda (,v* ...) ,expr) (printf "(lambda (") (for-each (lambda (v) (emit-var v) (printf " ")) v*) (printf ") ") (Expr expr) (printf ")")]))

  ;;; Ananlysis pass that uncovers the free variables within lambda expressions as the first
  ;;; step in performing closure conversion.
  (define-pass uncover-free : L6 (e) -> L7 ()
    (Expr : Expr (e) -> Expr (free*)
      [(quote ,c) (values `(quote ,c) '())]
      ;[,pr (values pr '())]
      [,v (values v (list v))]
      [(if ,[e1 free1*] ,[e2 free2*]) (values `(if ,e1 ,e2) (union free1* free2*))]
      [(if ,[e1 free1*] ,[e2 free2*] ,[e3 free3*]) (values `(if ,e1 ,e2 ,e3) (union free1* free2* free3*))]
      [(begin ,[e* free*] ... ,[e free**]) (values `(begin ,e* ... ,e) (union (fold-left union '() free**) free*))]
      [(set! ,v ,[e free*]) (values `(set! ,v ,e) free*)]
      [(primcall ,pr ,[e* free*] ...)
       (let ([free* (fold-left union '() free*)])
         (values `(primcall ,pr ,e* ...) free*))]
      [(,[e0 free*] ,[e1 free**] ...) (values `(,e0 ,e1 ...) (union (fold-left union '() free**) free*))]
      [(let ([,v* ,[e* free**]] ...) ,[e free*])
       (let ([free* (difference (union free* (union (fold-left union '() free**) free*)) v*)])
         (values `(let ([,v* ,e*] ...) ,e) free*))]
      [(letrec ([,v* ,[lbody* free**]] ...) ,[e free*])
       (let ([free* (difference (union free* (union (fold-left union '() free**) free*)) v*)])
         (values `(letrec ([,v* ,lbody*] ...) ,e) free*))]
      )
    (LambdaBody : LambdaBody (e) -> LambdaBody (free*)
      [(lambda (,v* ...) ,[expr free*])
       (let ([free* (difference free* v*)])
         (values `(lambda (,v* ...) (free (,free* ...) ,expr)) free*))])
    (let-values ([(expr free*) (Expr e)])
      (unless (null? free*) (error 'uncover-free "Unbound variables: " free*))
      expr))

  (define-pass convert-closures : L7 (e) -> L8 ()
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,v* (lambda (,v** ...)
                       (free (,v2** ...) ,[expr*]))] ...)
         ,[expr])
       (let ([label* (map unique-label v*)]
             [cp (map (lambda (_) (unique-name)) v*)])
         `(letrec ([,label* (lambda (,cp ,v** ...)
                              (bind-free (,cp ,v2** ...) ,expr*))] ...)
            (closures ((,v* ,label* ,v2** ...) ...) ,expr)))]
      [(,[e0] ,[e*] ...)
       (if (or (label? e0) (variable? e0))
           `(,e0 ,e* ...)
           (let ([tmp (unique-name 'tmp)])
             `(let ([,tmp ,e0])
                (,tmp ,tmp ,e* ...))))]))

  (define-pass introduce-procedure-primitives : L8 (e) -> L9 ()
    (definitions
      (define handle-procedure-set
        (lambda (name free* free-locs cp)
          (let loop ([free* free*] [n 0])
            (if (null? free*)
                '()
                (let ([expr (Expr (car free*) free-locs cp)])
                  (cons (with-output-language (L9 Expr)
                          `(procedure-set! ,name (quote ,n) ,expr))
                        (loop (cdr free*) (+ n 1)))))))))
    ; free-locs: a-list mapping uvars that appear free to their offset in the closure structure
    ; cp: code pointer, or false if we're not inside a function
    (Expr : Expr (e [free-locs '()] [cp #f]) -> Expr ()
      [(letrec ([,l0* ,lbody*]) ,[closure free-locs cp -> expr])
       (let ([lbody* (map LambdaBody lbody* l0* free-locs cp)])
         `(letrec ([,l0* ,lbody*] ...) ,expr))]
      [(,[e] ,[e*] ...)
       (if (label? e)
           `(,e ,e* ...)
           `((procedure-code ,e) ,e* ...))]
      [,v (let ([p (assq v free-locs)])
            (if p
                `(procedure-ref ,cp (quote ,(cdr p)))
                v))]
      )
    (Closure : Closure (closure free-locs cp) -> Expr ()
      ; v*: list of procedure names
      ; l*: list of labels for each procedure
      ; v**: list of lists of free captured by each closure
      [(closures ((,v* ,l* ,v** ...) ...) ,[expr])
       (let ([expr (Expr expr free-locs cp)]
             [procedure-set!* (fold-left append '() (map handle-procedure-set v* v** free-locs cp))])
         ; make-procedure takes the procedure's name, label, and number of free variables
         `(let ([,v* (make-procedure ,v* ,l* ,(map length v**))] ...)
            (begin
              ,procedure-set!* ...
              ,expr)))])
    (LambdaBody : LambdaBody (lbody label free-locs cp) -> LambdaBody ()
      [(lambda (,v* ...) (bind-free (,v1 ,v1* ...) ,expr))
       (letrec ([make-free-locs (lambda (ls n)
                                  (cond
                                   [(null? ls) '()]
                                   [else (cons (cons (car ls) n) (make-free-locs (cdr ls) (+ n 1)))]))])
         (let ([free-locs (make-free-locs v1* 0)])
           `(lambda (,v* ...) ,(Expr expr free-locs v1))))])
    )

  ;; This pass lifts all function definitions to the beginning of the program. After this pass,
  ;; letrecs are no longer Exprs. Instead, there's one letrec at the top of the program that
  ;; contains all the lambda expressions. 
  ;;
  ;; As with convert-complex-datum, it's much easier to keep track of the lambda expressions
  ;; we've already seen via mutation rather than multiple return values
  (define-pass lift-letrec : L9 (e) -> L10 ()
    (definitions
      (define label* '())
      (define lambda-expr* '()))
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,l* ,[lbody*]] ...) ,[expr])
       (begin
         (set! label* (append l* label*))
         (set! lambda-expr* (append lbody* lambda-expr*))
         expr)])
    (let ([e (Expr e)])
      `(letrec ([,label* ,lambda-expr*] ...) ,e)))

  ;; This pass splits Exrs into 3 cases depending on how they are used:
  ;; Predicates, Effects, and Values. It is this pass that implements the logic of
  ;; "any non #f value is true", for example.
  ;;
  ;; Several minor optimizations occur during this pass. Any non-effectful expr in
  ;; an Effect context can be removed. We can additional replace an expr like:
  ;; (if #t some-expr another-expr) with just some-expr.
  (define-pass normalize-context : L10 (e) -> L11 ()
    (ExprValue : Expr (e) -> Value ()
      [(if ,e1 ,[e2] ,[e3])
       (let ([e1 (ExprPred e1)])
         `(if ,e1 ,e2 ,e3))]
      [(begin ,e* ... ,[e])
       (let ([e* (map ExprEffect e*)])
         `(begin ,e* ... ,e))]
      [(let ([,x* ,e*] ...) ,e)
       (let ([e* (map ExprValue e*)]
             [e (ExprValue e)])
         `(let ([,x* ,e*] ...) ,e))]
      [(primcall ,pr ,e* ...) (guard (predicate-primitive? pr))
       (let ([e* (map ExprValue e*)])
         `(if (primcall ,pr ,e* ...) '#t '#f))]
      [(primcall ,pr ,e* ...) (guard (effect-primitive? pr))
       (let ([e* (map ExprValue e*)])
         `(begin (primcall ,pr ,e* ...) (void)))]
      [(primcall ,pr ,e* ...) (guard (value-primitive? pr))
       (let ([e* (map ExprValue e*)])
         `(primcall ,pr ,e* ...))]
      [(,[e0] ,[e*] ...) `(,e0 ,e* ...)]
      [(quote ,c) `(quote ,c)]
      )
    (ExprPred : Expr (e) -> Predicate ()
      [(quote ,c) (if (eq? c '#f) `(false) `(true))]
      [(begin ,e* ... ,[e])
       (let ([e* (map ExprEffect e*)])
         `(begin ,e* ... ,e))]
      [(let ([,x* ,e*] ...) ,[e])
       (let ([e* (ExprValue e*)])
         `(let ([,x* ,e*]) ,e))]
;      [(void) `(true)]
      [(primcall ,pr ,e* ...) (guard (predicate-primitive? pr))
       (let ([e* (ExprValue e*)])
         `(primcall ,pr ,e* ...))]
      [(primcall ,pr ,[e*] ...) (guard (effect-primitive? pr))
       (let ([e* (map ExprValue e*)])
         `(begin (primcall ,pr ,e* ...) (true)))]
      [(primcall ,pr ,e* ...) (guard (value-primitive? pr))
       (let ([e* (map ExprValue e*)])
         `(primcall ,pr ,e* ...))]
      [(,e0 ,e* ...)
       (let ([e0 (ExprValue e0)]
             [e* (map ExprValue e*)])
         `(,e0 ,e* ...))]
      [,x `(if (eq? ,x '#f) (false) (true))])
    (ExprEffect : Expr (e) -> Effect ()
      [(quote ,c) `(nop)]
      [(if ,e1 ,[e2] ,[e3])
       (let ([e1 (ExprPred e1)])
         `(if ,e1 ,e2 ,e3))]
      [(let ([,x* ,e*]) ,[e])
       (let ([e* (map ExprValue e*)])
         `(let ([,x* ,e*]) ,e))]
;      [(void) `(nop)]
      [(primcall ,pr ,e* ...) (guard (or (value-primitive? pr) (predicate-primitive? pr)))
       (error 'ExprEffect "NOP CASE")
       `(nop)]
      [(,e0 ,e* ...)
       (let ([e0 (ExprValue e0)]
             [e* (map ExprValue e*)])
         `(,e0 ,e* ...))]
      [,x (error 'ExprEffect "NOP CASE") `(nop)])
    (LambdaBody : LambdaBody (lbody) -> LambdaBody ()
      [(lambda (,v* ...) ,expr)
       `(lambda (,v* ...) ,(ExprValue expr))])
    (Program : Program (p) -> Program ()
      [(letrec ([,l* ,[lbody*]] ...) ,expr)
       (let ([expr (ExprValue expr)])
         `(letrec ([,l* ,lbody*] ...) ,expr))])
    )

  ;; This pass turns calls that implicitly require memory allocation (like cons), memory
  ;; references (like car and cdr), and memory mutation (like set-car!) into explicit calls
  ;; to alloc, mref, and mset!.
  (define-pass specify-memory-representation : L11 (e) -> L12 ()
    (Value : Value (e) -> Value ()
      [(primcall ,value-prim ,[v])
       (case value-prim
         [(car) `(mref ,v ,disp-car)]
         [(cdr) `(mref ,v ,disp-cdr)]
         [(procedure-code) `(mref ,v ,disp-procedure-code)])]
      [(primcall ,value-prim ,[v0] ,[v1])
       (case value-prim
         [(cons)
          (let ([tmp-car (make-tmp)]
                [tmp-cdr (make-tmp)]
                [tmp (make-tmp)])
            `(let ([,tmp-car ,v0]
                   [,tmp-cdr ,v1])
               (let ([,tmp (alloc ,size-pair)])
                 (begin
                   (mset! ,tmp ,disp-car ,tmp-car)
                   (mset! ,tmp ,disp-cdr ,tmp-cdr)
                   ,tmp))))]
         [(procedure-ref)
          (cond
           [(catullus-fixnum? v1)
            `(mref ,v0 ,(+ (disp-procedure-data) v1))]
           [else (error 'specify-representation "procedure-ref: received non-constant index")])]
         [(make-procedure)
          (let ([tmp (make-tmp)])
            (cond
             [(catullus-fixnum? v1)
              `(let ([,tmp (alloc ,(+ disp-procedure-code v1))])
                 (begin
                   (mset! ,tmp ,disp-procedure-code ,v0)
                   ,tmp))]
             [else (error 'specify-representation "make-procedure: received non-constant arguemnt")]))]
         [else `(primcall ,value-prim ,v0 ,v1)])])
    (Effect : Effect (e) -> Effect ()
      [(primcall ,effect-prim ,[v0] ,[v1])
       (case effect-prim
         [(set-car!) `(mset! ,v0 ,disp-car v1)]
         [(set-cdr!) `(mset! ,v0 ,disp-cdr v1)])]
      [(primcall ,effect-prim ,[v0] ,[v1] ,[v2])
       (case effect-prim
         [(procedure-set!)
          (cond
           [(catullus-fixnum? v1)
            `(mset! ,v0 ,(+ disp-procedure-data v1) ,v2)]
           [else (error 'specify-representation "procedure-set!: received non-constant argument")])])])
    )

  (define-pass remove-let : L12 (e) -> L13 ()
    (definitions
      (define generate-set!
        (lambda (x v)
          (with-output-language (L13 Effect)
            `(set! ,x ,v)))))
    (Value : Value (e) -> Value ()
      [(let ([,x* ,v*] ...) ,[v])
       (let* ([v* (map Value v*)]
              [set!-ls (map generate-set! x* v*)])
         `(begin
            ,set!-ls ...
            ,v))])
    (Effect : Effect (e) -> Effect ()
      [(let ([,x* ,v*] ...) ,[e])
       (let* ([v* (map Value v*)]
              [set!-ls (map generate-set! x* v*)])
         `(begin
            ,set!-ls ...
            ,e))])
    (Predicate : Predicate (e) -> Predicate ()
      [(let ([,x* ,v*] ...) ,[p])
       (let* ([v* (map Value v*)]
              [set!-ls (map generate-set! x* v*)])
         `(begin
            ,set!-ls ...
            ,p))])
    )

  (define-pass remove-complex-opera* : L13 (p) -> L14 ()
    (definitions
      (define make-value-begin
        (lambda (v v-extras)
          (with-output-language (L14 Value)
            (if (null? v-extras)
                v
                `(begin ,v-extras ... v)))))
      (define make-pred-begin
        (lambda (p p-extras)
          (with-output-language (L14 Predicate)
            (if (null? p-extras)
                p
                `(begin ,p-extras ... p)))))
      (define make-effect-begin
        (lambda (e e-extras)
          (with-output-language (L14 Effect)
            (if (null? e-extras)
                e
                `(begin ,e-extras ... e)))))
      (define fold-effect*
        (lambda (e* e*-extras)
          (fold-right (lambda (e e-extras accum) (append e-extras (list e) accum)) '() e* e*-extras))))
    (Value : Value (v) -> Value ('())
      [(if ,[p p-extras] ,[v1 v1-extras] ,[v2 v2-extras])
       `(if ,(make-pred-begin p p-extras)
            ,(make-value-begin v1 v1-extras)
            ,(make-value-begin v2 v2-extras))]
      [(begin ,e* ... ,v)
       (let-values ([(e* e*-extras) (map Effect e*)]
                    [(v v-extras) (Value v)])
         (values v (append (fold-effect* e* e*-extras) v-extras)))]
      [(primcall ,value-prim ,v* ...)
       (printf "PRIMCALL\n")
       (let-values ([(v* v*-extras) (map Value v*)])
         (values `(primcall ,value-prim ,v* ...)
                 (fold-right append '() v*-extras)))]
      [(,v ,v* ...)
       (let-values ([(v v-extras) (Value v)]
                    [(v* v*-extras) (map Value v*)])
         (values `(,v ,v* ...)
                 (append v-extras (fold-right append '() v*-extras))))]
      )
    (Predicate : Predicate (p) -> Predicate ('())
      [(if ,p0 ,p1 ,p2)
       (let-values ([(p0 p0-extras) (Predicate p0)]
                    [(p1 p1-extras) (Predicate p1)]
                    [(p2 p2-extras) (Predicate p2)])
         (values `(if ,p0 ,(make-pred-begin p1 p1-extras) ,(make-pred-begin p2 p2-extras))
                 p0-extras))]
      [(begin ,e* ... ,p)
       (let-values ([(e* e*-extras) (map Effect e*)]
                    [(p p-extras) (Predicate p)])
         (values p (append (fold-effect* e* e*-extras) p-extras)))]
      [(primcall ,pred-prim ,v* ...)
       (let-values ([(v* v*-extras) (map Value v*)])
         (values 
          `(primcall ,pred-prim ,v* ...)
          (fold-right append '() v*-extras)))]
      [(,v ,v* ...)
       (let-values ([(v v-extras) (Value v)]
                    [(v* v*-extras) (map Value v*)])
         (values `(,v ,v* ...)
                 (append v-extras (fold-right append '() v*-extras))))])
    (Effect : Effect (e) -> Effect ('())
      [(if ,p ,e0 ,e1)
       (let-values ([(p p-extras) (Predicate p)]
                    [(e0 e0-extras) (Effect e0)]
                    [(e1 e1-extras) (Effect e1)])
         (values `(if ,p ,(make-effect-begin e0 e0-extras) ,(make-effect-begin e1 e1-extras))
                 p-extras))]                 
      [(begin ,e* ... ,e)
       (let-values ([(e* e*-extras) (map Effect e*)]
                    [(e e-extras) (Effect e)])
         (values e (append (fold-effect* e* e*-extras) e-extras)))]
      [(primcall ,effect-prim ,v* ...)
       (let-values ([(v* v*-extras) (map Value v*)])
         (values `(primcall ,effect-prim ,v* ...)
                 (fold-right append '() v*-extras)))]
      [(,v ,v* ...)
       (let-values ([(v v-extras) (Value v)]
                    [(v* v*-extras) (map Value v*)])
         (values `(,v ,v* ...)
                 (append v-extras (fold-right append '() v*-extras))))])
    (Program : Program (p) -> Program ()
      [(letrec ([,l* (lambda (,x* ...) ,body*)] ...) ,body)
       (printf "PROGRAM\n")
       (printf "body: ~s\n" body)
       (let-values ([(body body-extras) (Value body)]
                    [(body* body*-extras) (if (null? body*) (values '() '()) (map Value body*))])
         (let ([body (make-value-begin body body-extras)]
               [body* (map make-value-begin body* body*-extras)])
           `(letrec ([,l* (lambda (,x* ...) ,body*)] ...) ,body)))]))

  (define-pass flatten-set! : L14 (p) -> L100 ()
    (flatten-value : Value (v uvar) -> Effect ()
      [(if ,[p] ,v1 ,v2)
       (let ([e1 (flatten-value v1 uvar)]
             [e2 (flatten-value v2 uvar)])
       `(if ,p ,e1 ,e2))]
      [(begin ,e* ... ,v)
       (let ([e* (map Effect e*)]
             [v (flatten-value v uvar)])
         `(begin ,e* ... ,v))]
      [(alloc ,i) `(set! ,uvar (alloc ,i))]
      [(primcall ,value-prim ,triv* ...) `(set! ,uvar (primcall ,value-prim ,triv* ...))]
      [(,triv ,triv* ...) `(set! ,uvar (,triv ,triv* ...))]
      [(quote ,c) `(set! ,uvar (quote ,c))]
      [,l `(set! ,uvar ,l)]
      [,x `(set! ,uvar ,x)])
    (Effect : Effect (e) -> Effect ()
      [(set! ,x ,v) (flatten-value v x)]))

  (define-pass generate-js : L100 (e) -> * ()
    (definitions
      (define format-args
        (lambda (args)
          (define args-help
            (lambda (args)
              (cond
               [(null? args) ""]
               [(null? (cdr args)) (car args)]
               [else (string-append (car args) ", " (args-help (cdr args)))])))
          (string-append "(" (args-help args) ")")))
      (define format-primcall
        (lambda (primcall args)
          (let ([args (map format-triv args)])
            (case primcall
              [(null?) (format "~a === null" (car args))]
              [(boolean?) (format "typeof ~a === 'boolean'" (car args))]
              [(pair?) (error 'format-primcall "pair? isn't supported yet")]
              [(fixnum?) (format "typeof ~a === 'number' && ~a <= ~a <= ~a" (car args) min-fixnum (car args) max-fixnum)]
              [(procedure?) (format "typeof ~a === 'function'" (car args))]
              [(=) (format "~a === ~a" (car args) (cadr args))]
              [(<) (format "~a < ~a" (car args) (cadr args))]
              [(<=) (format "~a <= ~a" (car args) (cadr args))]
              [(>=) (format "~a >= ~a" (car args) (cadr args))]
              [(>) (format "~a > ~a" (car args) (cadr args))]
              [(eq?) (format "~a == ~a" (car args) (cadr args))]
              [(+) (format "~a + ~a" (car args) (cadr args))]
              [(-) (format "~a - ~a" (car args) (cadr args))]
              [(*) (format "~a * ~a" (car args) (cadr args))]
              [(void) "undefined"]
              [(mref) (format "runtime.mref(~a)" (car args))]
              [else (error 'format-primcall (format "Unsupported primitive: ~a" primcall))]))))
      (define emit-primcall
        (lambda (primcall args)
          (printf "~a~%" (format-primcall primcall args))))
      (define format-var
        (lambda (v)
          (let ([prefix (unique-prefix v)]
                [suffix (unique-suffix v)])
            (string-append prefix "_" suffix))))
      )
    (format-rhs : Rhs (rhs) -> * (formatted-rhs)
     [(primcall ,value-prim ,triv* ...) (format-primcall value-prim triv*)]
     [(alloc ,i) (format "runtime.alloc(~a)" (number->string i))]
     [(mref ,i) (format "runtime.mref(~a)" (number->string i))]
     [(,triv ,triv* ...) (format "~a~a" (format-triv triv) (format-args triv*))]
     [,triv (format-triv triv)])
    (format-triv : Triv (triv) -> * (formatted-triv)
     [,i (number->string i)]
     [,l (symbol->string l)]
     [,x (format-var x)]
     [(quote ,c)
      (case c
        [(#t) "true"]
        [(#f) "false"]
        [(()) "null"]
        [else (format "~a" c)])]
     [else (error 'format-triv (format "Invalid triv: ~s" triv))]
     )
    (format-effect : Effect (e) -> * (formatted-effect)
      [(if ,p ,e1 ,e2)
       (let ([p (format-predicate p)]
             [e1 (format-effect e1)]
             [e2 (format-effect e2)])
         (format "(~a) : (~a) ? (~a)" p e1 e2))]
      [(begin ,e* ... ,e)
       (let ([e* (map format-effect e*)]
             [e (format-effect e)])
         (fold-left (lambda (this acc) (cons this acc)) e* (list e)))]
      [(set! ,x ,rhs)
       (format "~a = ~a;" (format-var x) (format-rhs rhs))]
      [(mset! ,v0 ,offset ,v1) (format "runtime.mset((~a + ~a), ~a)" (format-value v0) (number->string offset) (format-value v1))]
      [(primcall ,effect-prim ,triv* ...)
       (format-primcall effect-prim triv*)]
      [(,triv ,triv* ...)
       (format "~a~a;" (format-triv triv) (format-args triv*))]
      [(nop) ""])
    (format-predicate : Predicate (p) -> * (formatted-pred)
      [(false) "false"]
      [(true) "true"]
      [(if ,p1 ,p2 ,p3)
       (let ([p1 (format-predicate p1)]
             [p2 (format-predicate p2)]
             [p3 (format-predicate p3)])
         (string-append "(~a) : (~a)  ? (~a)" p1 p2 p3))]
      [(begin ,e* ... ,p)
       (let ([e* (map format-effect e*)]
             [p (format-predicate p)])
         (fold-left (lambda (e e*) (cons e e*)) e* (list p)))]
      [(primcall ,pred-prim ,triv* ...)
       (format-primcall pred-prim triv*)]
      [(,triv ,triv* ...) (format "~a~a" (format-triv triv) (format-args triv*))])
    (format-value : Value (v) -> * (formatted-value)
;      [(alloc ,i) (format "runtime.alloc(~a)" (number->string i))]
;      [(mref ,i) (format "runtime.mref(~a)" (number->string i))]
      [(if ,p ,v1 ,v2)
       (format "(~a) : (~a) ? (~a)" (format-predicate p) (format-value v1) (format-value v2))]
      [(begin ,e* ... ,v)
       (let ([e* (map format-effect e*)]
             [v (format-value v)])
         (fold-left (lambda (e e*) (cons e e*)) e* (list v)))]
      [(primcall ,value-prim ,triv* ...)
       (format-primcall value-prim triv*)]
      [,rhs (format-rhs rhs)])
      #|
      [,l (format "~a~%" l)]
      [,x (format-var x)]
      [(quote ,c)
       (case c
        [(#t) (format "true~%")]
        [(#f) (format "false~%")]
        [(()) (format "null~%")]
        [else (format "~a~%" c)])])
      |#
    (emit-function : LambdaBody (lbody label) -> * ()
      [(lambda (,x* ...) ,body)
       (printf "function ~a ~a{~%" label (format-args x*))
       (emit-value body)
       (printf "}~%~%")])
    (emit-value : Value (body) -> * ()
;      [(alloc ,i) (printf "runtime.alloc(~a);~%" (number->string i))]
;      [(mref ,i) (printf "runtime.mref(~a);~%" (number->string i))]
      [(if ,p ,v1 ,v2)
       (printf "if (~a) {~%" (format-predicate p))
       (emit-value v1)
       (printf "} else {~%")
       (emit-value v2)
       (printf "}~%")]
      [(begin ,e* ... ,v)
       (for-each emit-effect e*)
       (emit-value v)]
      [(primcall ,value-prim ,triv* ...)
       (emit-primcall value-prim triv*)]
      [(,triv ,triv* ...)
       (printf "~a~a;~%" (format-triv triv) (format-args triv*))]
      [,rhs (printf "~a~%" (format-rhs rhs))]
      #|
      [,l (printf "~a~%" l)]
      [,x (printf "~a~%" x)]
      [(quote ,c)
       (case c
        [(#t) (printf "true~%")]
        [(#f) (printf "false~%")]
        [(()) (printf "null~%")]
        [else (printf "~a~%" c)])]
      |#
      )
    (emit-effect : Effect (e) -> * ()
      [(mset! ,v0 ,offset ,v1) (printf "runtime.mset((~a + ~a), ~a);~%" (format-value v0) (number->string offset) (format-value v1))]
      [(if ,p ,e1 ,e2)
       (printf "if (~a) {~%" (format-predicate p))
       (emit-effect e1)
       (printf "} else {~%")
       (emit-effect e2)
       (printf "}~%")]
      [(begin ,e* ... ,e)
       (for-each emit-effect e*)
       (emit-effect e)]
      [(set! ,x ,rhs)
       (printf "~a = ~a;~%" (format-var x) (format-rhs rhs))]
      [(primcall ,effect-prim ,triv* ...)
       (emit-primcall effect-prim triv*)]
      [(,triv ,triv* ...)
       (printf "~a~a;~%" (format-triv triv) (format-args triv*))]
      [(nop) (printf "undefined")])
    (Program : Program (p) -> * ()
      [(letrec ([,l* ,lbody*] ...) ,body)
       (begin
         (printf "var runtime = require('./runtime.js');~%~%")
         (for-each emit-function lbody* l*)
         (emit-value body))])

    )

  ;;; a little helper shamelesly stolen from Andy Keep,
  ;;; who apparently shamelessly stole it from
  ;;; the Chez Scheme User's Guide.
  ;;; (I need it to use define-compiler, which I
  ;;; also shamelessly stole from Andy)
  (define-syntax with-implicit
    (syntax-rules ()
      [(_ (tid id ...) body0 ... body1)
       (with-syntax ([id (datum->syntax #'tid 'id)] ...)
         body0 ... body1)]))

  (define-syntax define-compiler
    (lambda (x)
      (syntax-case x ()
        [(_ name (pass unparser) ... emit-L5)
         (with-implicit (name all-passes trace-passes)
                        #`(begin
                            (define all-passes '(pass ... write-L5-to-file))
                            (define trace-passes
                              (let ([passes '()])
                                (case-lambda
                                  [() passes]
                                  [(x)
                                   (cond
                                    [(symbol? x)
                                     (unless (memq x all-passes)
                                       (error 'trace-passes "invalid pass name" x))
                                     (set! passes (list x))]
                                    [(list? x)
                                     (unless (for-all (lambda (x) (memq x all-passes)) x)
                                       (error 'trace-passes
                                              "one or more invalid pass names" x))
                                     (set! passes x)]
                                    [(eq? x #t) (set! passes all-passes)]
                                    [(eq? x #f) (set! passes '())]
                                    [else (error 'trace-passes
                                                 "invalid pass specifier" x)])])))
                            (define name
                              (lambda (x)
                                #,(let loop ([pass* #'(pass ...)]
                                             [unparser* #'(unparser ...)])
                                    (if (null? pass*)
                                        #'(begin
                                            (when (file-exists? "out.js") (delete-file "out.js"))
                                            (with-output-to-file "out.js"
                                              (lambda () (generate-js x)))
                                            (when (memq 'generate-js (trace-passes))
                                              (printf "output of pass ~a~%" 'generate-js)
                                              (call-with-input-file "out.js"
                                                (lambda (ip)
                                                  (let f ()
                                                    (let ([s (get-string-n ip 512)])
                                                      (unless (eof-object? s)
                                                        (display s)
                                                        (f)))))))
                                            (system "node -p < out.js > result") 
                                            (call-with-input-file "result" read))
                                        (with-syntax ([pass (car pass*)]
                                                      [unparser (car unparser*)])
                                          #`(let ([x (pass x)])
                                              (when (memq 'pass (trace-passes))
                                                (printf "output of pass ~a~%" 'pass)
                                                (pretty-print (unparser x)))
                                              #,(loop (cdr pass*)
                                                      (cdr unparser*))))))))))])))

  (define-compiler catullus-compile
    (parse-scheme unparse-L0)
    (remove-implicit-begin unparse-L1)
    (introduce-primcall unparse-L1.5)
    (convert-complex-datum unparse-L2)
    (uncover-assigned unparse-L3)
    (purify-letrec unparse-L4)
    (convert-assignments unparse-L5)
    (remove-anonymous-lambda unparse-L6)
    ;emit-L6
    (uncover-free unparse-L7)
    (convert-closures unparse-L8)
    (introduce-procedure-primitives unparse-L9)
    (lift-letrec unparse-L10)
    (normalize-context unparse-L11)
    (specify-memory-representation unparse-L12)
    (remove-let unparse-L13)
    (remove-complex-opera* unparse-L14)
    (flatten-set! unparse-L100)
    generate-js)

  (trace-passes #t)

  (language->s-expression L12)
  )
