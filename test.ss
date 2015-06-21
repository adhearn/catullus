(import (rnrs) (catullus))

;; Because javascript has different primitive values (e.g. false instead of #f),
;; we have to decide on a common set of values for comparison. I've chose the
;; javascript names, since it's easier to convert from scheme to javascript
(define make-canonical
  (lambda (value)
    (case value
      [(#t) 'true]
      [(#f) 'false]
      [(()) 'null]
      [else value])))

(define-syntax define-tests
  (syntax-rules ()
    [(_ name test* ...)
     (define name
       (list (cons (quote test*) (make-canonical (eval (quote test*)))) ...))]))

(define-tests simple-tests
  0)

(define-tests tests
  -1
  0
  1
  120
  -50000
  50000
  #t
  #f
  (+ 3 8)
  #|
  (- 18 3)
  (* 84 5)
  '()
  (null? '())
  (null? '(1 2 3))
  (null? (cons 1 #t))
  (pair? '())
  (pair? '(1 8 #t))
  (pair? 8)
  (pair? #t)
  (boolean? #t)
  (boolean? #f)
  (boolean? 17)
  (boolean? '())
  (boolean? (cons #t #f))
  (boolean? '(#t #f))
  (fixnum? 48)
  (fixnum? -834)
  (fixnum? #t)
  (fixnum? #f)
  (fixnum? '())
  (fixnum? '(1 2))
  (fixnum? (cons -45 12))
  (if #t -1 1)
  (if #f 38 (not #f))
  (if (and (> 8 4) (= 6 6)) #t #f)
  (let ([x 5]) (* x x))
  (letrec ([fact (lambda (x) (if (= x 0) 1 (* x (fact (- x 1)))))])
    (fact 5))
  (let ([x 5]) (set! x 8) x)
  (begin 5)
  (begin (let ([x 5]) (set! x 10) x) 12)
  (let ([x 5]
        [y 23]
        [z 17])
    (letrec ([sum (lambda (a b) (+ a b))]
             [set-z-sum! (lambda (c d) (set! z (sum c d)) z)])
      (set-z-sum! x y)
      z))
  (let ([test (lambda (x) (> x 10))]
        [num 100])
    (if (test num) (set! num 80) (set! num -80))
    num)
  (letrec ([fib (lambda (a) (if (= a 1) 1
                                (if (= a 2) 1
                                    (+ (fib (- a 1)) (fib (- a 2))))))])
    (fib 6))
  (letrec ([zero? (lambda (x) (= 0 x))]
           [fact (lambda (x k)
                   (if (zero? x)
                       (k 1)
                       (fact (- x 1)
                             (lambda (v) (k v)))))])
    (fact 5 (lambda (x) x)))
  (car '(1 2 #t))
  (cdr '(#t #t #t #f))
  (car (cdr '(1 2 #f)))
  (null? '(8 54 23))
  (null? '())
  (letrec ([length (lambda (ls) (if (null? ls) 0 (+ 1 (length (cdr ls)))))])
    (length '(1 2 3 4 5 6 7)))
  (letrec ([memq (lambda (x ls) (if (null? ls) #f (if (eq? x (car ls)) ls (memq x (cdr ls)))))])
    (let ([lst '(1 2 3 #t #f)])
      ((lambda (x) (if (memq x lst) lst (cons x lst))) 10)))
  (letrec ([memq (lambda (x ls) (if (null? ls) #f (if (eq? x (car ls)) ls (memq x (cdr ls)))))])
    (let ([lst '(1 2 3 #f #t #f)])
      ((lambda (x) (if (memq x lst) lst (cons x lst))) #t)))
  (letrec ([even? (lambda (x) (if (= x 0) #t
                                  (if (= x 1) #f
                                      (odd? (- x 1)))))]
           [odd? (lambda (x) (not (even? x)))])
    (even? 8))
  (letrec ([even? (lambda (x) (if (= x 0) #t
                                  (if (= x 1) #f
                                      (odd? (- x 1)))))]
           [odd? (lambda (x) (not (even? x)))])
    (odd? 8))
  (letrec ([even? (lambda (x) (if (=  x 0) #t
                                  (if (= x 1) #f
                                      (odd? (- x 1)))))]
           [odd? (lambda (x) (not (even? x)))])
    (even? 17))
  (letrec ([even? (lambda (x) (if (= x 0) #t
                                  (if (= x 1) #f
                                      (odd? (- x 1)))))]
           [odd? (lambda (x) (not (even? x)))])
    (odd? 17))
  (letrec ([make-ratio (lambda (n d) (cons n d))]
           [numerator (lambda (rat) (car rat))]
           [denominator (lambda (rat) (cdr rat))]
           [add-rat (lambda (r1 r2) (make-ratio (+ (* (numerator r1) (denominator r2))
                                                 (* (numerator r2) (denominator r1)))
                                              (* (denominator r1) (denominator r2))))])
    (add-rat (make-ratio 1 3) (make-ratio 3 8)))
  (letrec ([make-ratio (lambda (n d) (cons n d))]
           [numerator (lambda (rat) (car rat))]
           [denominator (lambda (rat) (cdr rat))]
           [mult-rat (lambda (r1 r2) (make-ratio (* (numerator r1) (numerator r2))
                                                 (* (denominator r2) (denominator r1))))])
    (mult-rat (make-ratio 1 3) (make-ratio 3 8)))
  (((lambda (x) (lambda (y) (+ x y))) 3) 4)
  (let ([abs (lambda (x) (if (< x 0) (- x) x))])
    (abs -5))
  |#
 )

(syntax-rules ()
  [(_ format-string (irritants ...))
   (format format-string irritants ...)])

; Not sure if this is the ideal way to handle exceptions, but it seems to work kinda ok
(define run-tests
  (lambda (tests)
    (printf "running tests...\n")
    (let loop ([tests tests]
               [count 0]
               [succeeded 0]
               [failed 0])
      (if (null? tests)
          (begin (printf "tests completed\n")
                 (printf "~s tests run, ~s succeeded, ~s failed" count succeeded failed))
          (let ([test (caar tests)]
                [expected (cdar tests)])
            (let ([catullus-output (guard (x [else (printf "ERROR: failed to compile, input: ~s\n(~s) ~s\n" test (condition-message x) (condition-irritants x))])
;            (let ([catullus-output (guard (x [else (printf "ERROR: failed to compile, input: ~s\n(~s) \n" test (format-list (condition-message x) (condition-irritants x)))])
                                          (catullus-compile test))])
;              (let ([actual (guard (x [else (printf "ERROR: failed to evaluate, input: ~s\noutput: ~s\n" test catullus-output)])
;                                   (eval catullus-output))])
                (if (equal? catullus-output expected)
                    ((printf "pass succeeded\n") (loop (cdr tests) (add1 count) (add1 succeeded) failed))
                    ((printf "ERROR: input: ~s\nexpected: ~s\nreceived: ~s\n" test expected catullus-output) (loop (cdr tests) (add1 count) succeeded (add1 failed))))))))))

