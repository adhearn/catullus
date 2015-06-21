(library (catullus helpers)
  (export constants variable? label? catullus-fixnum? constant? datum? primitive? predicate-primitive? effect-primitive? value-primitive? memory+effect-primitive? memory+value-primitive? primitives union intersection difference unique-name unique-label unique-prefix unique-suffix simple-dotimes disp-car disp-cdr disp-procedure-code disp-procedure-data size-pair min-fixnum max-fixnum)
  (import (rnrs))
  
  (define constants '(#t #f ()))

  ;(define primitives '(cons car cdr null? boolean? pair? fixnum? + - * = < <= > >= eq? void))

  ; Andy's method of making these alists with the car being the primitive name and the
  ; cdr being the number of args is pretty convenient, so I've stolen it.
  (define predicate-primitives '((null? . 1) (boolean? . 1) (pair? . 1) (fixnum? . 1)
                                 (procedure? . 1) (= . 2) (< . 2) (<= . 2) (> . 2) (>= . 2) (eq? .2)))
  
  (define effect-primitives '((procedure-set! . 3) (set-car! . 2) (set-cdr! . 2)))

  (define value-primitives '((+ . 2) (- . 2) (* . 2) (cons . 2) (make-procedure . 1) (car . 1)
                             (cdr . 1) (procedure-code . 2) (procedure-ref . 2) (void . 0)))

  (define alloc-value-primitives '((mref . 1)))

  (define primitives (append predicate-primitives effect-primitives value-primitives))

  (define predicate-primitive?
    (lambda (x)
      (assq x predicate-primitives)))

  (define effect-primitive?
    (lambda (x)
      (assq x effect-primitives)))

  (define value-primitive?
    (lambda (x)
      (assq x value-primitives)))

  (define memory-effect-primitives '((mset! . 3)))
  (define memory-value-primitives '((mref . 2)))

  (define memory+effect-primitive?
    (lambda (x)
      (assq x (append memory-effect-primitives effect-primitives))))

  (define memory+value-primitive?
    (lambda (x)
      (assq x (append memory-value-primitives value-primitives))))
      

  (define variable?
    (lambda (x)
      (symbol? x)))

  ;; Displacement Helpers
  (define disp-car 0)
  (define disp-cdr 1)
  (define disp-procedure-code 0)
  (define disp-procedure-data 1)

  ;; Size Helpers
  (define size-pair 2)

  ;; I only know how to handle 61-bit signed integers, so that's all this compiler will handle for now.
  (define catullus-fixnum?
    (lambda (x)
      (and (integer? x)
           (<= min-fixnum x max-fixnum))))

  (define max-fixnum (- (expt 2 60) 1))
  (define min-fixnum (- (expt 2 60)))

  (define constant?
    (lambda (x)
      (or (memq x constants)
          (catullus-fixnum? x))))

  (define datum?
    (lambda (x)
      (or (constant? x)
          (and (pair? x) (datum? (car x)) (datum? (cdr x))))))

  (define primitive?
    (lambda (x)
      (and (symbol? x)
           (assq x (append value-primitives effect-primitives predicate-primitives)))))

  (define label?
    (lambda (x)
      (and (symbol? x)
           (let ([string-list (reverse (string->list (symbol->string x)))])
             (letrec ([loop (lambda (ls seen-$ seen-num)
                              (cond
                               [(null? ls) #f]
                               [(char<=? #\0 (car ls) #\9) (loop (cdr ls) seen-$ #t)]
                               [(char=? (car ls) #\$) (if seen-num (loop (cdr ls) #t seen-num) #f)]
                               [(and seen-$ seen-num) #t]
                               [else #f]))])
               (loop string-list #f #f))))))

  ; Set union on two lists, but doesn't check if they're pairs before performing various list operations on them.
  (define union2
    (lambda (x y)
      (cond
       [(null? x) y]
       [(null? y) x]
       [(member (car x) y) (cons (car x) (union2 (cdr x) y))]
       [else (union2 (cdr x) y)])))
                 

  (define union
    (case-lambda
      [() '()]
      [(x) x]
      [(x y) (union2 x y)]
      [(x . y) (union2 x (apply union y))]))

  ; Set intersection on two lists.
  (define intersection
    (lambda (x y)
      (cond
       [(null? x) x]
       [(null? y) y]
       [(member (car x ) y) (cons (car x) (intersection (cdr x) y))]
       [else (intersection (cdr x) y)])))

  ; Set difference on two lists. We use remq, since this will be used only on lists of symbols
  (define difference
    (lambda (x y)
      (cond
       [(null? y) x]
       [else (difference (remq (car y) x) (cdr y))])))

  (define unique-count 0)

  (define next-unique
    (lambda ()
      (set! unique-count (+ 1 unique-count))
      unique-count))

  (define unique-name
    (lambda (prefix)
      (string->symbol (string-append (symbol->string prefix) "." (number->string (next-unique))))))

  (define unique-label
    (lambda (uvar)
      (let ([prefix (unique-prefix uvar)])
        (string->symbol (string-append (symbol->string prefix) "$" (number->string next-unique))))))
                                       

  (define unique-prefix
    (lambda (x)
      (letrec ([char-ls (string->list (symbol->string x))]
               [loop (lambda (ls comparison-char)
                       (if (char=? (car ls) comparison-char)
                           '()
                           (cons (car ls) (loop (cdr ls) comparison-char))))])
            (if (label? x)
                (list->string (loop char-ls #\$))
                (list->string (loop char-ls #\.))))))

  ; Simpler way than unique-prefix, just finds the location of the first occurrence of the
  ; key character, then returns the rest of the string
  (define unique-suffix
    (lambda (x)
      (letrec ([char-ls (string->list (symbol->string x))]
               [loop (lambda (ls char)
                       (cond
                        [(null? ls) ""]
                        [(char=? (car ls) char) (list->string (cdr ls))]
                        [else (loop (cdr ls) char)]))])
        (if (label? x)
            (loop char-ls #\$)
            (loop char-ls #\.)))))
               

  ; An extrmely simple, non-macro dotimes that collects the results of call function f with
  ; no arguments n times. Do not depend on the order that results are returned!
  (define simple-dotimes
    (lambda (n f)
      (if (= n 0)
          '()
          (cons (f) (simple-dotimes (- n 1) f)))))
)
