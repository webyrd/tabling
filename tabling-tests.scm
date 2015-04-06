(load "vanilla-r5-minimal.scm")

;(import (tabling) (rnrs) (rnrs eval))

(define remove-answer
  (lambda (x ls)
    (cond
      ((null? ls) '())
      ((equal? (car ls) x) (cdr ls))
      (else (cons (car ls) (remove-answer x (cdr ls)))))))

(define answer-set-equal?
  (lambda (ls1 ls2)
    (cond
      ((null? ls1) (null? ls2))
      ((member (car ls1) ls2)
       (answer-set-equal? (cdr ls1) (remove-answer (car ls1) ls2)))
      (else #f))))

(define (void) (if #f #f))

;(define make-engine (eval 'make-engine (environment '(scheme))))

(define skipped-tests
  (let ((ls '()))
    (case-lambda
      (() ls)
      ((t) (set! ls (cons t ls))))))

(define-syntax print
  (syntax-rules (nl)
    ((_ nl . x) (begin (newline) (print . x)))
    ((_ x0 . x) (begin (display x0) (print . x)))
    ((_) (void))))

(define-syntax define-test
  (syntax-rules ()
    ((_ name (pl ...) expr (pr ...) (do-name args ...))
     (define-syntax name
       (syntax-rules (skip)
         ((_ title (skip reason) pl ... expr pr ...) (begin (print "WARNING: SKIPPING " title nl) (skipped-tests (cons title reason))))
         ((_ title skip pl ... expr pr ...) (name title (skip "no reason") pl ... expr pr ...))
         ((_ title pl ... expr pr ...)
          (begin
            (print "Testing " title "...")
            (do-name args ... (lambda (string . irr) (apply error 'title string 'expr irr)))
            (print " done" nl))))))))

(define-test dtest () expr () (do-dtest (lambda () expr)))
(define-syntax dtest (syntax-rules () ((_ title x ...) (test title (skip "no engines") #f #f))))

(define-test test () expr (expe) (do-test expe equal? expr))
(define-test mtest () expr (expe) (do-test expe answer-set-equal? expr))
(define-test ptest (passes?) expr () (do-test 'ptest (lambda (e c) (passes? c)) expr))
(define-test ftest () expr (expe) (do-ftest (lambda () expr) expe))
(define-test vtest (pred?) expr () (do-vtest (lambda () expr) pred?))

(define do-dtest
  (lambda (thunk error)
    (define max-ticks (exact 1e8))
    ((make-engine thunk)
     max-ticks
     (lambda (t v) (error "failed to diverge" (- max-ticks t) v))
     not)))

(define do-test
  (lambda (expected equal? computed error)
    (unless (equal? expected computed)
      (print nl "expected: " expected)
      (print nl "computed: " computed nl)
      (error "failed"))))

(define do-ftest
  (lambda (th expe error)
    (unless (null? expe)
      (let ((p (th)))
        (cond
          ((null? p) (error "failed to produce answers" expe))
          ((member (car p) expe) (do-ftest (cdr p) (remove-answer (car p) expe) error))
          (else (do-ftest (cdr p) expe error)))))))

(define do-vtest
  (lambda (th pred? error)
    (guard
      (con
        ((pred? con))
        (else (error "failed to produce appropriate error" con)))
      (begin (th) (error "no error")))))


; canonical program for tabling
; These path examples from 'Memoing for Logic Programs' by David S. Warren
(mtest "path-1"
  (letrec ((arc (lambda (x y)
                  (conde
                    ((== x 'a) (== y 'b))
                    ((== x 'c) (== y 'b))
                    ((== x 'b) (== y 'd)))))
           (path (lambda (x y)
                   (conde
                     ((arc x y))
                     ((fresh (z)
                        (arc x z)
                        (path z y)))))))
    (run* (q)
      (path 'a q)))
  '(b d))

(mtest "path-1-tabled"
  (letrec ((arc (lambda (x y)
                  (conde
                    ((== x 'a) (== y 'b))
                    ((== x 'c) (== y 'b))
                    ((== x 'b) (== y 'd)))))
           (path (tabled (x y)
                   (conde
                     ((arc x y))
                     ((fresh (z)
                        (arc x z)
                        (path z y)))))))
    (run* (q)
      (path 'a q)))
  '(b d))

(define nato
  (lambda (n)
    (conde
      [(== 'z n)]
      [(fresh (n-1)
         (== `(s ,n-1) n)
         (nato n-1))])))

(define nat-tabledo
  (tabled (n)
    (conde
      [(== 'z n)]
      [(fresh (n-1)
         (== `(s ,n-1) n)
         (nat-tabledo n-1))])))

(define pluso
  (lambda (n m out)
    (conde
      [(== 'z n) (== m out)]
      [(fresh (n-1 res)
         (== `(s ,n-1) n)
         (== `(s ,res) out)
         (pluso n-1 m res))])))

(define plus-tabledo
  (tabled (n m out)
    (conde
      [(== 'z n) (== m out)]
      [(fresh (n-1 res)
         (== `(s ,n-1) n)
         (== `(s ,res) out)
         (plus-tabledo n-1 m res))])))


; run* diverges
(mtest "path-2"
  (letrec ((arc (lambda (x y)
                  (conde
                    ((== x 'a) (== y 'b))
                    ((== x 'b) (== y 'a))
                    ((== x 'b) (== y 'd)))))
           (path (lambda (x y)
                   (conde
                     ((arc x y))
                     ((fresh (z)
                        (arc x z)
                        (path z y)))))))
    (run 10 (q)
      (path 'a q)))
  '(b a d b a d b a d b))

(mtest "path-2-tabled"
  (letrec ((arc (lambda (x y)
                  (conde
                    ((== x 'a) (== y 'b))
                    ((== x 'b) (== y 'a))
                    ((== x 'b) (== y 'd)))))
           (path (tabled (x y)
                   (conde
                     ((arc x y))
                     ((fresh (z)
                        (arc x z)
                        (path z y)))))))
    (run* (q)
      (path 'a q)))
  '(b a d))


;; (mtest "test-subsumption-master-call"
;;   (let ((f (tabled (z)
;;              (conde
;;                ((== z 5))
;;                ((== z 5))))))
;;     (run* (q)
;;       (f q)))
;;   '(5))

;; (mtest "test-lack-of-subsumption-slave-call"
;;   (let ((f (tabled (z) (== z 5))))
;;     (run* (q)
;;       (conde
;;         ((f q))
;;         ((f q)))))
;;   '(5 5))

;; (mtest "test-subsumption-master-call-lambda"
;;   (let ((f (lambda (z)
;;              (conde
;;                ((== z 5))
;;                ((== z 5))))))
;;     (run* (q)
;;       (f q)))
;;   '(5 5))

;; (mtest "test-lack-of-subsumption-slave-call-lambda"
;;   (let ((f (lambda (z) (== z 5))))
;;     (run* (q)
;;       (conde
;;         ((f q))
;;         ((f q)))))
;;   '(5 5))

;; (mtest "test-subsumption-master-call-a"
;;   (let ((f (tabled (z)
;;              (conde
;;                ((fresh (x) (== z `(5 . ,x))))
;;                ((== z `(5)))))))
;;     (run* (q)
;;       (f q)))
;;   '((5 . _.0)))

;; (mtest "test-subsumption-master-call-b"
;;   (let ((f (tabled (z)             
;;              (conde
;;                ((== z `(5)))
;;                ((fresh (x) (== z `(5 . ,x))))))))
;;     (run* (q)
;;       (f q)))
;;   '((5 . _.0)))

;; (mtest "test-subsumption-master-call-c"
;;   (let ((f (tabled (z)
;;              (fresh (x)
;;                (conde
;;                  ((== z `(5 . ,x)))
;;                  ((== z `(5))))))))
;;     (run* (q)
;;       (f q)))
;;   '((5 . _.0)))

;; (mtest "test-subsumption-master-call-d"
;;   (let ((f (tabled (z)             
;;              (fresh (x)
;;                (conde
;;                  ((== z `(5)))
;;                  ((== z `(5 . ,x))))))))
;;     (run* (q)
;;       (f q)))
;;   '((5 . _.0)))


(mtest "why-we-dont-table-full-substitutions-non-tabled-a"
  (let ((f (lambda (z) (== z 6))))
    (run* (q)
      (fresh (x y)
        (conde
          ((== x 5) (f y))
          ((f y)))
        (== `(,x ,y) q))))
  '((5 6) (_.0 6)))

(mtest "why-we-dont-table-full-substitutions-non-tabled-b"
  (let ((f (tabled (z) (== z 6))))
    (run* (q)
      (fresh (x y)
        (conde
          ((== x 5) (f y))
          ((f y)))
        (== `(,x ,y) q))))
  '((5 6) (_.0 6)))

(mtest "not-closed-not-tabled"
  (run* (q)
    (fresh (x y)
      (let ((f (lambda (z) (fresh () (== x 5) (== z 6)))))
        (fresh ()
          (conde
            ((f y))
            ((f y))) 
          (== `(,x ,y) q)))))
  '((5 6) (5 6)))

(mtest "not-closed-tabled"
  (run* (q)
    (fresh (x y)
      (let ((f (tabled (z) (fresh () (== x 5) (== z 6)))))
        (fresh ()
          (conde
            ((f y))
            ((f y))) 
          (== `(,x ,y) q)))))
  '((5 6) (_.0 6)))

(mtest "not-closed-not-tabled-b"
  (run* (q)
    (fresh (x y)
      (let ((f (lambda (z) (fresh () (== x 5) (== z 6)))))
        (conde
          ((f y) (== `(,x ,y) q))
          ((f y) (== `(,x ,y) q))))))
  '((5 6) (5 6)))

(mtest "not-closed-tabled-b"
  (run* (q)
    (fresh (x y)
      (let ((f (tabled (z) (fresh () (== x 5) (== z 6)))))
        (conde
          ((f y) (== `(,x ,y) q))
          ((f y) (== `(,x ,y) q))))))
  '((5 6) (_.0 6)))


(mtest "cant-break-subsumption-without-occurs-check-a"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f x))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-b"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f x)
        (f x))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-c"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f `(,x)))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-d"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f `(,x))
        (f `(,x)))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-e"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f `(,x))
        (f x))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-f"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (fresh (x)
        (f x)
        (f `(,x)))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-g"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (f q)
      (f `(,q))))
  '(_.0))

(mtest "cant-break-subsumption-without-occurs-check-h"
  (letrec ((f (tabled (ignore) (== #f #f))))
    (run* (q)
      (f `(,q))
      (f q)))
  '(_.0))

(mtest "occurs-check-0"
  (run* (q)
    (fresh (x)
      (== q `(,x))
      (== x q)))
  '())

(mtest "non-tabled 0s fixed"
  (letrec
    ((f (lambda (x)
          (conde
            ((== x '()))
            ((fresh (y)
               (== x `(0 . ,y))
               (f y)))))))
    (run* (q)
      (fresh (a b)
        (== q `(,a ,b))
        (f q)
        (f b))))
  '())

(mtest "tabled 0s fixed"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x '()))
            ((fresh (y)
               (== x `(0 . ,y))
               (f y)))))))
    (run* (q)
      (fresh (a b)
        (== q `(,a ,b))
        (f q)
        (f b))))
  '())

(ftest "nest 3"
  (letrec
    ((nest (tabled (x)
             (conde
               ((== x '()))
               ((fresh (y)
                  (== x `(,y))
                  (nest y)))))))
    (run+ (q) (nest q)))
  '(() (()) ((()))))

(ftest "listo"
  (letrec
    ((listo (tabled (ls)
              (conde
                ((== ls '()))
                ((fresh (a d)
                   (== ls `(,a . ,d))
                   (listo d)))))))
    (run+ (q) (listo q)))
  '(() (_.0) (_.0 _.1) (_.0 _.1 _.2) (_.0 _.1 _.2 _.3) (_.0 _.1 _.2 _.3 _.4)))

(let ((f (tabled (x y) (== x y))))
  (mtest "simple f"
    (run* (q) (f 2 q))
    '(2)))

(let ((f (tabled (x y) (conde
                         ((== x y))
                         ((== x #f))))))
  (mtest "simple f conde"
    (run* (q) (f q #t))
    '(#t #f)))

(test "simple recursion"
  (letrec ((f (tabled (x)
                (conde
                  ((== x 0))
                  ((f x))))))
    (run 1 (q) (f q)))
  '(0))

(ftest "skipped recursion"
  (letrec ((g (tabled (x y)
                (conde ((== x y)) ((g x y))))))
    (run+ (q) (g 2 q)))
  '(2))

(mtest "no duplicates"
  (letrec ((g (tabled (x y)
                (conde ((g x y)) ((== x y))))))
    (run* (q) (g 2 q)))
  '(2))

(mtest "appendo gt 7 right order"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((fresh (a d res)
                     (== l `(,a . ,d))
                     (== out `(,a . ,res))
                     (appendo d s res)))))))
    (run 7 (q)
      (fresh (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "appendo gt 7" (skip "no true conjunction")
                                        ; FAILS - don't have true conjunction when there is sharing of variables between the conjuncts
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((fresh (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 7 (q)
      (fresh (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t))
    ((cake) (with ice d t))
    ((cake with) (ice d t))
    ((cake with ice) (d t))
    ((cake with ice d) (t))
    ((cake with ice d t) ())))

(mtest "appendo non-tabled 7 nothing" (skip "no true conjunction") ; tabling isn't the only problem
  (letrec
    ((appendo (lambda (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((fresh (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 7 (q)
      (fresh (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t))
    ((cake) (with ice d t))
    ((cake with) (ice d t))
    ((cake with ice) (d t))
    ((cake with ice d) (t))
    ((cake with ice d t) ())))

(mtest "non-multi prefix 3"
  (letrec
    ((f (tabled (l p)
          (conde
            ((== p '()))
            ((fresh (a d r)
               (== l `(,a . ,d))
               (== p `(,a . ,r))
               (f d r)))))))
    (run 3 (q) (f '(cake) q)))
  '(() (cake)))

(mtest "comconj0" (skip "no true conjunction")
  (run* (q) (let l () (conde ((l)) ((l)))) (== #t #f))
  '())

(mtest "comconj1" (skip "no true conjunction")
  (run* (q) (let l () (conde ((l)) ((let l () (conde ((l)) ((l))))))) (== #t #f))
  '())

(mtest "comconj2" (skip "no true conjunction")
  (run* (q)
    (let l () (conde ((l)) ((l))))
    (let l () (conde ((l)) ((l))))
    (== #f #t))
  '())

(mtest "tails"
  (letrec
    ((g (lambda (x y)
          (conde
            ((== x y))
            ((fresh (a d)
               (== x `(,a . ,d))
               (g d y)))))))
    (run* (q)
      (g '(a b c d e) q)))
  '((a b c d e) (b c d e) (c d e) (d e) (e) ()))

;; (let ((check-run
;;         (lambda (con)
;;           (and (assertion-violation? con)
;;             (eq? (condition-who con) 'run)))))

;;   (vtest "run error 0" check-run
;;     (run -10 (q) (== q 5)))

;;   (vtest "run error 1" check-run
;;     (run 0 (q) (== q 5)))

;;   (vtest "run error 2" check-run
;;     (run 'hello (q) (== q 5))))

(test 'm1
  (answer-set-equal? '() '())
  #t)

(test 'm2
  (answer-set-equal? '(a) '())
  #f)

(test 'm3
  (answer-set-equal? '() '(a))
  #f)

(test 'm4
  (answer-set-equal? '(a) '(a a))
  #f)

(test 'm5
  (answer-set-equal? '(a a) '(a))
  #f)

(test 'm6
  (answer-set-equal? '(a a) '(a a))
  #t)

(test 'm7
  (answer-set-equal? '(a b a) '(a b))
  #f)

(test 'm8
  (answer-set-equal? '(a b a) '(b a a))
  #t)

(test 'm9
  (answer-set-equal? '(a b) '(a b a))
  #f)

(test 'm10
  (answer-set-equal?
    '((c a) (a a) (a b) (a c) (b a) (b b) (b c))
    '((a c) (c a)))
  #f)

(test 'm11
  (answer-set-equal?
    '((a c) (b a) (c a))
    '((c a) (a c)))
  #f)

(mtest "serious call"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x 0))
            ((g x)))))
     (g (tabled (x)
          (conde
            ((== x 1))
            ((== x 2))))))
    (run* (q) (f q)))
  '(0 1 2))

(test "tabled definition"
  (letrec
    ((g (tabled (x y)
          (conde ((== x y))
            ((g x y))))))
    #t)
  #t)

(letrec ((g (tabled (x y)
           (conde ((== x y)) ((g x y))))))
  (mtest "simple g"
    (run 2 (q) (g 2 q))
    '(2)))

(mtest "mutual recursion"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x 0))
            ((g x)))))
     (g (tabled (x)
          (conde
            ((== x 1))
            ((f x))))))
    (run* (q) (f q)))
  '(0 1))

(ftest "simple listo"
  (letrec
    ((listo (tabled (ls)
              (conde
                ((== ls '()))
                ((fresh (a d)
                   (== ls `(,a . ,d))
                   (listo d)))))))
    (run+ (q) (listo q)))
  '(()))

(letrec ((g (tabled (x y)
           (conde ((== x y)) ((g x y))))))
  (mtest "simple g 3"
    (run 3 (q) (g 2 q))
    '(2)))

(mtest "Guo Gupta 2008 CLSS Example 1"
  (letrec
    ((r (tabled (x y)
          (conde
            ((fresh (z) (r x z) (p z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))
            ((== `(,x ,y) `(b c)))))))
    (run* (x) (r 'a x)))
  '(a c b))

(mtest "Guo Gupta 2008 CLSS Example 1 Extra Tabling"
  (letrec
    ((r (tabled (x y)
          (conde
            ((fresh (z) (r x z) (p z y)))
            ((p x y)))))
     (p (tabled (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))
            ((== `(,x ,y) `(b c)))))))
    (run* (x) (r 'a x)))
  '(a c b))

(mtest "Guo Gupta 2001 LNCS Example 3"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((fresh (z)  (r x z) (r z y)))
            ((p x y) (q y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(a d)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (y)
          (conde ((== y 'b)) ((== y 'c))))))
    (run* (y) (r 'a y)))
  '(c b))

(mtest "Sagonas Swift Example"
  (letrec
    ((p (tabled (x y)
          (conde
            ((fresh (z) (p x z) (e z y)))
            ((e x y) (q y)))))
     (e (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(a d)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b))
            ((== x 'c))))))
    (run* (z) (p 'a z)))
  '(b c))

(ftest "Fig 21 non-tabled run 10" ; search strategy dependent
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((fresh (y) (p x y)))))))
    (run+ (q) (fresh (x y) 
                (== q `(,x ,y))
                (p x y))))
  '((c a) (a a) (a b) (a c) (b a) (b b) (b c)))

(ftest "Sagonas Swift Fig 21 no tabling" ; search strategy dependent
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((fresh (y) (p x y)))))))
    (run+ (q) (fresh (x y) 
                (== q `(,x ,y))
                (p x y))))
  '((a c) (a a)))

(mtest 'a1
  (run 3 (q) (== q 5) (== q 5))
  '(5))

(mtest 'a2
  (run 5 (q) (conde ((== q 3) (== q 4)) ((== q 5))))
  '(5))

(mtest 'a3
  (run 5 (q) (conde ((== q 3) (== q 3)) ((== q 5))))
  '(3 5))

(mtest 'a4
  (run 10 (q)
    (conde ((== q 3)) ((== q q)))
    (conde ((== q 3)) ((== q 4))))
  '(3 3 4))

(ftest "Simplified^2 non-tabled Guo Gupta 2001 LNCS Example 3"
 (letrec
   ((r (lambda (x y)
         (conde
           ((fresh (z) (r x z) (r z y)))
           ((== `(,x ,y) `(a b)))
           ((== `(,x ,y) `(b c)))))))
   (run+ (y) (r 'a y)))
 '(c b))

(mtest "Simplified^2 tabled Guo Gupta 2001 LNCS Example 3"
 (letrec
   ((r (tabled (x y)
         (conde
           ((fresh (z) (r x z) (r z y)))
           ((== `(,x ,y) `(a b)))
           ((== `(,x ,y) `(b c)))))))
   (run* (y) (r 'a y)))
 '(c b))

(mtest "Fig 21 really simplified"
  (letrec
    ((r (lambda (x)
          (conde
            ((== x 'c))
            ((r x))))))
    (run 1 (q) (r q)))
  '(c))

(mtest "Fig 21 simplified tabled"
  (letrec
    ((q (tabled (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (tabled (x)
          (conde
            ((== x 'c))
            ((r x))))))
    (run* (p)
      (fresh (x y)
        (== p `(,x ,y))
        (q x)
        (r y))))
  '((a c) (b c)))

(mtest "Simplified Guo Gupta 2001 LNCS Example 3"
  (letrec
    ((r (tabled (x y)
          (conde
            ((fresh (z) (r x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run* (y) (r 'a y)))
  '(c b))

(ftest "Simplified non-tabled Guo Gupta 2001 LNCS Example 3"
  (letrec
    ((r (lambda (x y)
          (conde
            ((fresh (z) (r x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run+ (y) (r 'a y)))
  '(c b))

(mtest "Guo Gupta 2001 LNCS Example 2"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((fresh (z)
               (conde
                 ((r x z) (p z y))
                 ((r x z) (q z y)))))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c))))))
     (q (lambda (x y)
          (== `(,x ,y) `(c d)))))
    (run* (y) (r 'a y)))
  '(d c b))

(mtest "Guo Gupta 2001 LNCS Example 4"
  (letrec 
    ((r (tabled (x y)
          (conde
            ((fresh (z) (p x z) (r z y)))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b a)))))))
    (run 10 (y) (r 'a y)))
  '(a b))

(mtest "Warren Figure 4"
  (letrec 
    ((path (tabled (x y)
             (conde
               ((arc x y))
               ((fresh (z) (arc x z) (path z y))))))
     (arc (lambda (x y)
            (conde
              ((== `(,x ,y) `(a b)))
              ((== `(,x ,y) `(b a)))
              ((== `(,x ,y) `(b d)))))))
    (run* (a) (path 'a a)))
  '(b a d))

(mtest "Guo Gupta 2008 CLSS Example 4"
  (letrec
    ((r (tabled (x y)
          (conde
            ((fresh (z)
               (conde
                 ((r x z) (q z y))
                 ((r x z) (p z y)))))
            ((p x y)))))
     (p (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(c d))))))
     (q (lambda (x y)
          (== `(,x ,y) `(b c)))))
    (run* (y) (r 'a y)))
  '(d c b))

(mtest "Zhou Sato Example"
  (letrec
    ((p (tabled (x y)
          (conde
            ((fresh (z) (p x z) (e z y)))
            ((e x y)))))
     (e (lambda (x y)
          (conde
            ((== `(,x ,y) `(a b)))
            ((== `(,x ,y) `(b c)))))))
    (run 10 (q) (p 'a q)))
  '(b c))

(mtest "Sagonas Swift Fig 12"
  (letrec
    ((a (tabled (x y)
          (conde
            ((c x y))
            ((fresh (z)  (b x z) (c z y))))))
     (b (tabled (x y)
          (conde
            ((d x y))
            ((fresh (z) (a x z) (c z y))))))
     (c (lambda (x y)
          (conde
            ((== `(,x ,y) '(0 1)))
            ((== `(,x ,y) `(1 2))))))
     (d (lambda (x y)
          (conde
            ((== `(,x ,y) '(0 1)))
            ((== `(,x ,y) `(1 2)))))))
    (run* (x) (a 0 x)))
  '(1 2))

(mtest "Sagonas Swift Fig 21 no tabling no recursion"
  (letrec
    ((p (lambda (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (lambda (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (lambda (x)
          (== x 'c))))
    (run 10 (q) (fresh (x y)
                  (== q `(,x ,y))
                  (p x y))))
  '((a c) (b c) (c a)))

(ftest "Sagonas Swift Fig 21 no tabling simplified"
  (letrec
    ((p (lambda (x y) (fresh () (q x) (r y))))
     (q (lambda (x) (== x 'a)))
     (r (lambda (x)
          (conde
            ((== x 'c))
            ((fresh (y) (p x y)))))))
    (run+ (q) (fresh (x y)
                 (== q `(,x ,y))
                 (p x y))))
  '((a c)))

(mtest "Sagonas Swift Fig 21"
  (letrec
    ((p (tabled (x y)
          (conde
            ((q x) (r y))
            ((== `(,x ,y) '(c a))))))
     (q (tabled (x)
          (conde
            ((== x 'a))
            ((== x 'b)))))
     (r (tabled (x)
          (conde
            ((== x 'c))
            ((fresh (y) (p x y)))))))
    (run 10 (q) (fresh (x y)
                    (== q `(,x ,y))
                    (p x y))))
  '((c a) (a a) (a b) (a c) (b a) (b b) (b c)))

(mtest "fg1"
  (letrec
    ((f (tabled (x p)
          (conde
            ((== x 0) (== p '()))
            ((fresh (q) (g x q) (== p `(1 . ,q)))))))
     (g (tabled (x q)
          (conde
            ((== x 1) (== q '()))
            ((f x q))))))
    (run 10 (q) (f 2 q)))
  '())

(mtest "fg2"
  (letrec
    ((f (tabled (x p)
          (fresh (q)
            (conde
              ((== x 0) (== p `(z . ,q)))
              ((g x q) (== p `(g . ,q)))))))
     (g (tabled (x p)
          (fresh (q)
            (conde
              ((== x 1) (== p `(o . ,q)))
              ((f x q) (== p `(f . ,q))))))))
    (run* (q) (f 2 q)))
  '())

(ftest "fg3"
  (letrec
    ((f (tabled (x p)
          (fresh (q)
            (conde
              ((== x 0) (== p `(z . ,q)))
              ((g x q) (== p `(g . ,q)))))))
     (g (tabled (x p)
          (fresh (q)
            (conde
              ((== x 1) (== p `(o . ,q)))
              ((f x q) (== p `(f . ,q))))))))
    (run+ (q) (f 1 q)))
  '((g o . _.0) (g f g o . _.0) (g f g f g o . _.0)))

(ftest "ab1"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((fresh (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run+ (q)
      (fresh (i o r)
        (== q `(,i ,o ,r))
        (b i o r))))
  '(((0 . _.0) _.0 z)))

(mtest "bobo0nt"
  (letrec
    ((b (lambda (i o)
          (conde
            ((== i `(0 . ,o)))
            ((fresh (bo) (b i o) (b o bo)))))))
    (run 2 (q)
      (fresh (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) (0 . _.0))))

(mtest "bobo0" ;(skip "subsumption")
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((fresh (bo) (b i o) (b o bo)))))))
    (run 2 (q)
      (fresh (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)))

(mtest "bio0"
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((fresh (bo) (b i bo) (b bo o)))))))
    (run 2 (q)
      (fresh (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) _.0)))

(mtest "ab0"
  (letrec
    ((b (tabled (i o)
          (conde
            ((== i `(0 . ,o)))
            ((fresh (bo) (b i bo) (a bo o))))))
     (a (tabled (i o)
          (conde ((a i o)) ((b i o))))))
    (run 2 (q)
      (fresh (i o)
        (== q `(,i ,o))
        (b i o))))
  '(((0 . _.0) _.0)
    ((0 0 . _.0) _.0)))

(mtest "ab2"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((fresh (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run 1 (q)
      (fresh (i o r)
        (== q `(,i ,o ,r))
        (b i o r))))
  '(((0 . _.0) _.0 z)))

(mtest "ab3"
  (letrec
    ((b (tabled (i o r)
          (conde
            ((== i `(0 . ,o)) (== r 'z))
            ((fresh (bo br ar)
               (== r `(ba ,br ,ar))
               (b i bo br)
               (a bo o ar))))))
     (a (tabled (i o r)
          (conde ((a i o r)) ((b i o r))))))
    (run 1 (q)
      (fresh (i o r _.0)
        (== q `(,i ,o ,r))
        (b i o r)
        (== q `((0 0 . ,_.0) (0 . ,_.0) z)))))
  '(((0 0 . _.0) (0 . _.0) z)))

(mtest "structural alwayso 2 non-tabled" ; succeeds with duplicates (see below)
  (letrec
    ((alwayso (lambda (x)
                (conde
                  ((== #f #f))
                  ((alwayso `(,x)))))))
    (run 2 (q)
      (alwayso q)))
  '(_.0 _.0))

(mtest "structural alwayso 1" ; NOTE run 2 diverges because there is only one answer and the changing structure defeats the tabling
  (letrec
    ((alwayso (tabled (x)
                (conde
                  ((== #f #f))
                  ((alwayso `(,x)))))))
    (run 1 (q)
      (alwayso q)))
  '(_.0))

(mtest "appendo gt 6"
  (letrec
    ((appendo (tabled (l s out)
                (conde
                  ((== '() l) (== s out))
                  ((fresh (a d res)
                     (== l `(,a . ,d))
                     (appendo d s res)
                     (== out `(,a . ,res))))))))
    (run 6 (q)
      (fresh (x y)
        (appendo x y '(cake with ice d t))
        (== q `(,x ,y)))))
  '((() (cake with ice d t)) ((cake) (with ice d t)) ((cake with) (ice d t)) ((cake with ice) (d t)) ((cake with ice d) (t)) ((cake with ice d t) ())))

(mtest "alwayso many answers"
  (letrec
    ((alwayso (tabled (x)
                (conde
                  ((== '() x))
                  ((fresh (y)
                     (== `(,y) x)
                     (alwayso y)))))))
    (run 10 (q) (alwayso q)))
  '(() (()) ((())) (((()))) ((((())))) (((((())))))
    ((((((())))))) (((((((()))))))) ((((((((()))))))))
    (((((((((())))))))))))

(mtest "subsumption 1"
  (letrec
    ((r (tabled (a b o)
          (conde
            ((== a #t))
            ((== a #f))
            ((r b a o)))
          (== o `(,a ,b)))))
    (run* (z) (fresh (x y) (r x y z))))
  '((#t _.0) (#f _.0)))

(mtest "subsumption 2"
  (letrec
    ((r (tabled (a b o)
          (== o `(,a ,b))
          (conde
            ((== a #t))
            ((== a #f))
            ((r b a o))))))
    (run* (z) (fresh (x y) (r x y z))))
  '((#t _.0) (#f _.0)))

;; (ftest "radar"
;;   (let-syntax
;;     ((e-over-timesteps
;;        (lambda (o)
;;          (syntax-case o ()
;;            ((_ e-blips (x ...))
;;             (with-syntax 
;;               (((xa ...) (generate-temporaries #'(x ...)))
;;                ((xd ...) (generate-temporaries #'(x ...))))
;;               #'(lambda (x ...)
;;                   (let f ((x x) ...)
;;                     (conde
;;                       ((== x '()) ...)
;;                       ((fresh (xa ... xd ...)
;;                          (== x `(,xa . ,xd)) ...
;;                          (e-blips xa ...)
;;                          (f xd ...))))))))))))
;;     (letrec
;;       ((e-random-position
;;          (lambda (v)
;;            (fresh (x y) (== v `(,x ,y))
;;              (e-member x (range 0 maximum-coordinate))
;;              (e-member y (range 0 maximum-coordinate)))))
;;        (e-member
;;          (lambda (x ls)
;;            (fresh (a d) (== ls `(,a . ,d))
;;              (conde ((== a x)) ((e-member x d))))))
;;        (range
;;          (case-lambda
;;            ((a b)
;;             (let f ((b (- b 1)) (r '()))
;;               (if (= b a) `(,a . ,r)
;;                 (f (- b 1) `(,b . ,r)))))
;;            ((b) (range 1 b))))
;;        (maximum-coordinate 19)
;;        (e-observed-blips
;;          (lambda (ps gs os)
;;            (conde
;;              ((== gs '()) (== os '()))
;;              ((fresh (id gd px py od)
;;                 (== gs `(,id . ,gd))
;;                 (== os `((,px ,py) . ,od))
;;                 (conde
;;                   ((== id #f) (e-random-position `(,px ,py)))
;;                   ((project (id ps)
;;                      (cond
;;                        ((assv id ps)
;;                         => (lambda (p)
;;                              (let ((f (lambda (x px)
;;                                         (let ((g (lambda (s)
;;                                                    (conde
;;                                                      ((== px (s x 1)))
;;                                                      ((== px (s x 2)))))))
;;                                           (conde ((== px x)) ((g +)) ((g -)))))))
;;                                (fresh () (f (cadr p) px) (f (caddr p) py)))))
;;                        (else (== #t #f))))))
;;                 (e-observed-blips ps gd od))))))
;;        (e-observed-sequence (e-over-timesteps e-observed-blips (pt gt ot))))
;;       (run+ (q)
;;         (e-observed-sequence
;;           '(((0 0 0) (1 1 3) (2 2 3))
;;             ((0 3 3) (1 1 2) (2 5 3))
;;             ((0 6 6) (1 1 1) (2 8 3)))
;;           '((1 2) (0 1 2) (0 1 #f))
;;           q))))
;;   '((((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 1)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (1 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 2)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 2) (0 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 7) (1 1) (0 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 4)) ((6 6) (1 1) (0 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 3)))
;;     (((1 3) (2 4)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (0 0)))
;;     (((1 3) (2 3)) ((3 3) (1 2) (5 3)) ((6 6) (1 1) (1 1)))))

(mtest "testc11.tex-1" 
  (run* (q) (== #f #t))
  `())

(mtest "testc11.tex-2"   
  (run* (q)
    (== #t q))
  `(#t))

(mtest "testc11.tex-3"   
  (run* (q) 
    (== #f #t)
    (== #t q))
  `())

(mtest "testc11.tex-4"   
  (run* (q) 
    (== #t #t) 
    (== #t q))
  (list #t))

(mtest "testc11.tex-5"   
  (run* (q) 
    (== #t #t) 
    (== #t q))
  `(#t))

(mtest "testc11.tex-6"   
  (run* (r) 
    (== #t #t) 
    (== 'corn r))
  (list 'corn))

(mtest "testc11.tex-7"   
  (run* (r) 
    (== #t #t) 
    (== 'corn r))
  `(corn))

(mtest "testc11.tex-8"   
  (run* (r)
    (== #f #t)
    (== 'corn r))
  `())

(mtest "testc11.tex-9"   
  (run* (q) 
    (== #t #t) 
    (== #f q))
  `(#f))

(mtest "testc11.tex-10" 
  (run* (x)
    (let ((x #f))
      (== #t x)))
  '())

(mtest "testc11.tex-11" 
  (run* (q)
    (fresh (x)
      (== #t x)
      (== #t q)))
  (list #t))

(mtest "testc11.tex-12" 
  (run* (q)
    (fresh (x)
      (== x #t)
      (== #t q)))
  (list #t))

(mtest "testc11.tex-13" 
  (run* (q)
    (fresh (x)
      (== x #t)
      (== q #t)))
  (list #t))

(mtest "testc11.tex-14"   
  (run* (x)
    (== #t #t))
  (list `_.0))

(mtest "testc11.tex-15"   
  (run* (x)
    (let ((x #f))
      (fresh (x)
        (== #t x))))
  `(_.0))

(mtest "testc11.tex-16" 
  (run* (r)
    (fresh (x y)
      (== (cons x (cons y '())) r)))
  (list `(_.0 _.1)))

(mtest "testc11.tex-17" 
  (run* (s)
    (fresh (t u)
      (== (cons t (cons u '())) s)))
  (list `(_.0 _.1)))

(mtest "testc11.tex-18" 
  (run* (r)
    (fresh (x)
      (let ((y x))
        (fresh (x)
          (== (cons y (cons x (cons y '()))) r)))))
  (list `(_.0 _.1 _.0)))

(mtest "testc11.tex-19" 
  (run* (r)
    (fresh (x)
      (let ((y x))
        (fresh (x)
          (== (cons x (cons y (cons x '()))) r)))))
  (list `(_.0 _.1 _.0)))

(mtest "testc11.tex-20" 
  (run* (q) 
    (== #f q)
    (== #t q))
  `())

(mtest "testc11.tex-21"   
  (run* (q) 
    (== #f q)
    (== #f q))
  '(#f))

(mtest "testc11.tex-22" 
  (run* (q)
    (let ((x q))
      (== #t x)))
  (list #t))

(mtest "testc11.tex-23" 
  (run* (r)
    (fresh (x)
      (== x r)))
  (list `_.0))

(mtest "testc11.tex-24" 
  (run* (q)
    (fresh (x)
      (== #t x)
      (== x q)))
  (list #t))

(mtest "testc11.tex-25" 
  (run* (q)
    (fresh (x)
      (== x q)
      (== #t x)))
  (list #t))

(mtest "testc11.tex-26" 
  (run* (q)
    (fresh (x)
      (== (eq? x q) q)))
  (list #f))

(mtest "testc11.tex-27" 
  (run* (q)
    (let ((x q))
      (fresh (q)
        (== (eq? x q) x))))
  (list #f))

(mtest "testc13.tex-fail1"
  (run* (q)
    (conde 
      ((== #t #f) (== #f #f)) 
      ((== #f #f) (== #t #f))))
  '())

(test "testc13.tex-succeed1"
  (not
    (null?
      (run* (q)
        (conde
          ((== #t #f) (== #t #f))
          ((== #t #t) (== #t #t))))))
  #t)
  
(test "testc13.tex-succeed2"
  (not
    (null?
      (run* (q)
        (conde
          ((== #t #t) (== #t #t))
          ((== #t #t) (== #t #f))))))
  #t)
  

(mtest "testc11.tex-30" 
  (run* (x)
    (conde
      ((== 'olive x) (== #t #t))
      ((== 'oil x) (== #t #t))))
  `(olive oil))

(ftest "testc11.tex-31" 
  (run+ (x)
    (conde
      ((== 'olive x) (== #t #t))
      ((== 'oil x) (== #t #t))))
  `(olive))

(mtest "testc11.tex-32" 
(run* (x)
  (conde
    ((== 'virgin x) (== #t #f))
    ((== 'olive x) (== #f #f))
    ((== #f #f) (== #f #f))
    ((== 'oil x) (== #f #f))))
`(olive _.0 oil))

(mtest "testc13.tex-conde1"
  (run* (x)
    (conde
      ((== 'olive x) (== #f #f))
      ((== #f #f) (== #f #f))
      ((== 'oil x) (== #f #f))))
  `(olive _.0 oil))
  
(ftest "testc11.tex-33" 
  (run+ (x)
    (conde
      ((== 'extra x) (== #f #f))
      ((== 'virgin x) (== #t #f))
      ((== 'olive x) (== #f #f))
      ((== 'oil x) (== #f #f))))
  `(extra olive))

(mtest "testc11.tex-34" 
  (run* (r)
    (fresh (x y)
      (== 'split x)
      (== 'pea y)
      (== (cons x (cons y '())) r)))
  (list `(split pea)))

(mtest "testc11.tex-35" 
  (run* (r)
    (fresh (x y)
      (conde
        ((== 'split x) (== 'pea y))
        ((== 'navy x) (== 'bean y)))
      (== (cons x (cons y '())) r)))
  `((split pea) (navy bean)))

(mtest "testc11.tex-36" 
  (run* (r)
    (fresh (x y)
      (conde
        ((== 'split x) (== 'pea y))
        ((== 'navy x) (== 'bean y)))
      (== (cons x (cons y (cons 'soup '()))) r)))
  `((split pea soup) (navy bean soup)))

(let ((teacupo
        (lambda (x)
          (conde
            ((== 'tea x) (== #f #f))
            ((== 'cup x) (== #f #f))))))

  (mtest "testc23.tex-14"   
    (run* (r)
      (conde
        ((teacupo r) (== #f #f))
        ((== #f r) (== #f #f))))
    `(#f tea cup))

  (mtest "testc11.tex-37"   
    (run* (x)
      (teacupo x))
    `(tea cup))

  (mtest "testc11.tex-38"   
    (run* (r)
      (fresh (x y)
        (conde
          ((teacupo x) (== #t y) (== #f #f))
          ((== #f x) (== #t y)))
        (== (cons x (cons y '())) r)))
    `((#f #t) (tea #t) (cup #t))))

(mtest "testc11.tex-39"   
  (run* (r)                                                                      
    (fresh (x y z)                                                              
      (conde                                                                    
        ((== y x) (fresh (x) (== z x)))                                         
        ((fresh (x) (== y x)) (== z x)))                                        
      (== (cons y (cons z '())) r)))
  `((_.0 _.1) (_.0 _.1)))

(mtest "testc11.tex-40"
  (run* (r)                                                                      
    (fresh (x y z)                                                              
      (conde                                                                    
        ((== y x) (fresh (x) (== z x)))                                         
        ((fresh (x) (== y x)) (== z x)))
      (== #f x)
      (== (cons y (cons z '())) r)))
  `((#f _.0) (_.0 #f)))

(mtest "testc11.tex-41" 
  (run* (q)
    (let ((a (== #t q))
          (b (== #f q)))
      b))
  '(#f))

(mtest "testc11.tex-42" 
  (run* (q)
    (let ((a (== #t q))
          (b (fresh (x)
               (== x q)
               (== #f x)))
          (c (conde
               ((== #t q) (== #f #f))
               ((== #f #f) (== #f q)))))
      b))
  '(#f))

(mtest "testc12.tex-2" 
  (run* (r)
    (fresh (y x)
      (== `(,x ,y) r)))
  (list `(_.0 _.1)))

(mtest "testc12.tex-3" 
  (run* (r)
    (fresh (v w)
      (== (let ((x v) (y w)) `(,x ,y)) r)))
  `((_.0 _.1)))

(let ((caro (lambda (p a)
              (fresh (d)
                (== (cons a d) p)))))

  (mtest "testc12.tex-6" 
    (run* (r)
      (caro `(a c o r n) r))
    (list 'a))

  (mtest "testc12.tex-8"   
    (run* (q) 
      (caro `(a c o r n) 'a)
      (== #t q))
    (list #t))

  (mtest "testc12.tex-10" 
    (run* (r)
      (fresh (x y)
        (caro `(,r ,y) x)
        (== 'pear x)))
    (list 'pear))

  (mtest "testc12.tex-11"   
    (cons 
      (car `(grape raisin pear))
      (car `((a) (b) (c))))
    `(grape a))

  (mtest "testc12.tex-12" 
    (run* (r)
      (fresh (x y)
        (caro `(grape raisin pear) x)
        (caro `((a) (b) (c)) y)
        (== (cons x y) r)))
    (list `(grape a)))

  (mtest "testc12.tex-13"   
    (cdr `(grape raisin pear))
    `(raisin pear))

(let ((cdro (lambda (p d)
              (fresh (a)
                (== (cons a d) p)))))

  (mtest "testc12.tex-15" 
    (run* (r)
      (fresh (v)
        (cdro `(a c o r n) v)
        (caro v r)))
    (list 'c))

  (mtest "testc12.tex-17" 
    (run* (r)
      (fresh (x y)
        (cdro `(grape raisin pear) x)
        (caro `((a) (b) (c)) y)
        (== (cons x y) r)))
    (list `((raisin pear) a)))

  (mtest "testc12.tex-18"   
    (run* (q) 
      (cdro '(a c o r n) '(c o r n)) 
      (== #t q))
    (list #t))

  (mtest "testc12.tex-20" 
    (run* (x)
      (cdro '(c o r n) `(,x r n)))
    (list 'o))

  (mtest "testc12.tex-22" 
    (run* (l)
      (fresh (x) 
        (cdro l '(c o r n))
        (caro l x)
        (== 'a x)))
    (list `(a c o r n)))

(let ((conso (lambda (a d p) (== (cons a d) p))))

  (mtest "testc12.tex-23" 
    (run* (l)
      (conso '(a b c) '(d e) l))
    (list `((a b c) d e)))

  (mtest "testc12.tex-24" 
    (run* (x)
      (conso x '(a b c) '(d a b c)))
    (list 'd))

  (mtest "testc12.tex-26" 
    (run* (r)
      (fresh (x y z)
        (== `(e a d ,x) r)
        (conso y `(a ,z c) r)))
    (list `(e a d c)))

  (mtest "testc12.tex-27" 
    (run* (x)
      (conso x `(a ,x c) `(d a ,x c)))
    (list 'd))

  (mtest "testc12.tex-29" 
    (run* (l)
      (fresh (x)
        (== `(d a ,x c) l)
        (conso x `(a ,x c) l)))
    (list `(d a d c)))

  (mtest "testc12.tex-30" 
    (run* (l)
      (fresh (x)
        (conso x `(a ,x c) l)
        (== `(d a ,x c) l)))
    (list `(d a d c)))

  (mtest "testc12.tex-31" 
    (run* (l)
      (fresh (d x y w s)
        (conso w '(a n s) s)
        (cdro l s)
        (caro l x)
        (== 'b x)
        (cdro l d)
        (caro d y)
        (== 'e y)))
    (list `(b e a n s)))

(let ((nullo (lambda (x) (== '() x))))

  (mtest "testc12.tex-34" 
    (run* (q)
      (nullo `(grape raisin pear))
      (== #t q))
    `())

  (mtest "testc12.tex-35" 
    (run* (q)
      (nullo '())
      (== #t q))
    `(#t))

  (mtest "testc12.tex-36"   
    (run* (x) 
      (nullo x))
    `(()))

(let ((eqo (lambda (x y) (== x y))))

  (mtest "testc12.tex-39" 
    (run* (q)
      (eqo 'pear 'plum)
      (== #t q))
    `())

  (mtest "testc12.tex-40" 
    (run* (q)
      (eqo 'plum 'plum)
      (== #t q))
    `(#t))

  (mtest "testc12.tex-46"   
    (run* (r) 
      (fresh (x y)
        (== (cons x (cons y 'salad)) r)))
    (list `(_.0 _.1 . salad)))

(let ((pairo (lambda (p)
               (fresh (a d)
                 (conso a d p)))))

  (mtest "testc12.tex-47" 
    (run* (q)
      (pairo (cons q q))
      (== #t q))
    `(#t))

  (mtest "testc12.tex-48" 
    (run* (q)
      (pairo '())
      (== #t q))
    `())

  (mtest "testc12.tex-49" 
    (run* (q)
      (pairo 'pair)
      (== #t q))
    `())

  (mtest "testc12.tex-50"   
    (run* (x) 
      (pairo x))
    (list `(_.0 . _.1)))

  (mtest "testc12.tex-51"   
    (run* (r) 
      (pairo (cons r 'pear)))
    (list `_.0))

(letrec
  ((listo
     (lambda (l)
       (conde
         ((nullo l) (== #f #f))
         ((pairo l)
          (fresh (d)
            (cdro l d)
            (listo d)))))))

  (mtest "testc14.tex-5" 
    (run* (x)
      (listo `(a b ,x d)))
    (list `_.0))

(mtest "testc14.tex-6" 
  (run 1 (x)
    (listo `(a b c . ,x)))
  (list `()))


(dtest "testc14.tex-7"
  (run* (x)
    (listo `(a b c . ,x))))


(mtest "testc14.tex-8" 
  (run 5 (x)
    (listo `(a b c . ,x)))
  `(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)))

  (letrec
    ((lolo (lambda (l)
             (conde
               ((nullo l) (== #f #f))
               ((fresh (a) 
                  (caro l a)
                  (listo a))
                (fresh (d)
                  (cdro l d)
                  (lolo d)))))))

    (mtest "testc14.tex-9" 
      (run 1 (l)                                                                       
        (lolo l))                                                                     
      `(()))

    (mtest "testc14.tex-10" 
      (run* (q)
        (fresh (x y) 
          (lolo `((a b) (,x c) (d ,y)))
          (== #t q)))
      (list #t))

    (mtest "testc14.tex-11" 
      (run 1 (q)
        (fresh (x)
          (lolo `((a b) . ,x))
          (== #t q)))
      (list #t))

    (mtest "testc14.tex-12" 
      (run 1 (x)
        (lolo `((a b) (c d) . ,x)))
      `(()))

    (ftest "testc14.tex-13" 
      (run+ (x)
        (lolo `((a b) (c d) . ,x)))
      `(()
        (()) 
        ((_.0))
        (() ())
        ((_.0 _.1)))))

  (let ((twinso
          (lambda (s)
            (fresh (x y)
              (conso x y s)
              (conso x '() y)))))

    (mtest "testc14.tex-14" 
      (run* (q)
        (twinso '(tofu tofu))
        (== #t q))

      (list #t))

    (mtest "testc14.tex-15" 
      (run* (z) 
        (twinso `(,z tofu)))
      (list `tofu))

    (letrec
      ((loto
         (lambda (l)
           (conde
             ((nullo l) (== #f #f))
             ((fresh (a)
                (caro l a)
                (twinso a))
              (fresh (d)
                (cdro l d)
                (loto d)))))))

      (mtest "testc14.tex-16" 
        (run 1 (z)
          (loto `((g g) . ,z)))
        (list `()))

      (mtest "testc14.tex-17" 
        (run 5 (z)
          (loto `((g g) . ,z)))
        '(()
          ((_.0 _.0))
          ((_.0 _.0) (_.1 _.1))
          ((_.0 _.0) (_.1 _.1) (_.2 _.2))
          ((_.0 _.0) (_.1 _.1) (_.2 _.2) (_.3 _.3))))

      (mtest "testc14.tex-18" 
        (run 5 (r)
          (fresh (w x y z)
            (loto `((g g) (e ,w) (,x ,y) . ,z))
            (== `(,w (,x ,y) ,z) r)))
        '((e (_.0 _.0) ())
          (e (_.0 _.0) ((_.1 _.1)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2) (_.3 _.3)))
          (e (_.0 _.0) ((_.1 _.1) (_.2 _.2) (_.3 _.3) (_.4 _.4)))))

      (mtest "testc14.tex-19" 
        (run 3 (out)
          (fresh (w x y z)
            (== `((g g) (e ,w) (,x ,y) . ,z) out)
            (loto out)))
        `(((g g) (e e) (_.0 _.0))
          ((g g) (e e) (_.0 _.0) (_.1 _.1))
          ((g g) (e e) (_.0 _.0) (_.1 _.1) (_.2 _.2)))))


    (letrec
      ((listofo
         (lambda (predo l)
           (conde
             ((nullo l) (== #f #f))
             ((fresh (a)
                (caro l a)
                (predo a))
              (fresh (d)
                (cdro l d)
                (listofo predo d)))))))

      (mtest "testc14.tex-20" 
        (run 3 (out)
          (fresh (w x y z)
            (== `((g g) (e ,w) (,x ,y) . ,z) out)
            (listofo twinso out)))
        `(((g g) (e e) (_.0 _.0))
          ((g g) (e e) (_.0 _.0) (_.1 _.1))
          ((g g) (e e) (_.0 _.0) (_.1 _.1) (_.2 _.2)))))))

  (letrec
    ((membero
       (lambda (x l)
         (conde
           ((nullo l) (== #t #f))
           ((fresh (a)
              (caro l a)
              (== a x))
            (== #f #f))
           ((== #f #f)
            (fresh (d)
              (cdro l d)
              (membero x d)))))))

    (mtest "testc14.tex-22"   
      (run* (q) 
        (membero 'olive `(virgin olive oil))
        (== #t q))
      (list #t))

    (ptest "testc14.tex-23"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) `(hummus with pita))))
      (run 1 (y)
        (membero y `(hummus with pita))))

    (ptest "testc14.tex-24"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) '(with pita))))
      (run 1 (y) 
        (membero y `(with pita))))

    (mtest "testc14.tex-25"   
      (run 1 (y) 
        (membero y `(pita)))
      (list `pita))

    (mtest "testc14.tex-26"   
      (run* (y) 
        (membero y `()))
      `())

    (mtest "testc14.tex-27"   
      (run* (y) 
        (membero y `(hummus with pita)))
      `(hummus with pita))

    (mtest "testc14.tex-28"   
      (run* (x) 
        (membero 'e `(pasta ,x fagioli)))
      (list `e))

    (mtest "testc14.tex-29"   
      (run 1 (x) 
        (membero 'e `(pasta e ,x fagioli)))
      (list `_.0))

    (ptest "testc14.tex-30"   
      (lambda (c)
        (and (list? c) (= (length c) 1)
          (memq (car c) '(e _.0))))
      (run 1 (x) 
        (membero 'e `(pasta ,x e fagioli))))

    (mtest "testc14.tex-31"   
      (run* (r)
        (fresh (x y)
          (membero 'e `(pasta ,x fagioli ,y))
          (== `(,x ,y) r)))
      `((e _.0) (_.0 e)))

    (ftest "testc14.tex-32"   
      (run+ (l) (membero 'tofu l))
      `((tofu . _.0)))

    (dtest "testc14.tex-33"
      (run* (l) (membero 'tofu l)))

    (ftest "testc14.tex-34" 
      (run+ (l)
        (membero 'tofu l))
      `((tofu . _.0)
        (_.0 tofu . _.1)
        (_.0 _.1 tofu . _.2)
        (_.0 _.1 _.2 tofu . _.3)
        (_.0 _.1 _.2 _.3 tofu . _.4))))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x) (cdro l '()))
           ((fresh (d)
              (cdro l d)
              (pmembero x d)))))))

    (ftest "testc14.tex-35"   
      (run+ (l)
        (pmembero 'tofu l))
      `((tofu)
        (_.0 tofu)
        (_.0 _.1 tofu)
        (_.0 _.1 _.2 tofu)
        (_.0 _.1 _.2 _.3 tofu)))

    (mtest "testc14.tex-36"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t)))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x)
            (conde
              ((cdro l '()))
              ((== #f #f))))
           ((fresh (d)
              (cdro l d)
              (pmembero x d)))))))

    (mtest "testc14.tex-37"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t #t #t)))

  (letrec
    ((pmembero
       (lambda (x l)
         (conde
           ((caro l x)
            (conde
              ((cdro l '()))
              ((fresh (a d)
                 (cdro l `(,a . ,d))))))
           ((fresh (d)
              (cdro l d)
              (pmembero x d)))))))

    (mtest "testc14.tex-38"   
      (run* (q)
        (pmembero 'tofu `(a b tofu d tofu))
        (== #t q))
      `(#t #t))

    (ftest "testc14.tex-39" 
      (run+ (l)
        (pmembero 'tofu l))
      `((tofu)
        (tofu _.0 . _.1)
        (_.0 tofu)
        (_.0 tofu _.1 . _.2)
        (_.0 _.1 tofu)
        (_.0 _.1 tofu _.2 . _.3)
        (_.0 _.1 _.2 tofu)
        (_.0 _.1 _.2 tofu _.3 . _.4)
        (_.0 _.1 _.2 _.3 tofu)
        (_.0 _.1 _.2  _.3 tofu _.4 . _.5 )
        (_.0 _.1 _.2 _.3 _.4 tofu)
        (_.0 _.1 _.2 _.3 _.4 tofu _.5 . _.6))))

  (letrec
    ((memo
       (lambda (x l out)
         (conde
           ((caro l x) (== l out))
           ((fresh (d)
              (cdro l d)
              (memo x d out)))))))

    (ftest "testc15.tex-7"   
      (run+ (out) 
        (memo 'tofu `(a b tofu d tofu e) out))
      `((tofu d tofu e)))

    (ftest "testc15.tex-8"   
      (run+ (out) 
        (fresh (x)
          (memo 'tofu `(a b ,x d tofu e) out)))
      `((tofu d tofu e)))

    (mtest "testc15.tex-9"   
      (run* (r)
        (memo r
          `(a b tofu d tofu e)
          `(tofu d tofu e)))
      (list `tofu))

    (mtest "testc15.tex-10" 
      (run* (q)
        (memo 'tofu '(tofu e) '(tofu e))
        (== #t q))
      (list #t))

    (mtest "testc15.tex-11" 
      (run* (q)
        (memo 'tofu '(tofu e) '(tofu))
        (== #t q))
      `())

    (mtest "testc15.tex-12" 
      (run* (x)
        (memo 'tofu '(tofu e) `(,x e)))
      (list `tofu))

    (mtest "testc15.tex-13" 
      (run* (x)
        (memo 'tofu '(tofu e) `(peas ,x)))
      `())

    (mtest "testc15.tex-14"   
      (run* (out) 
        (fresh (x) 
          (memo 'tofu `(a b ,x d tofu e) out)))
      `((tofu d tofu e) (tofu e)))

    (ftest "testc15.tex-15" 
      (run+ (z)
        (fresh (u)
          (memo 'tofu `(a b tofu d tofu e . ,z) u)))
      `(_.0
         _.0
         (tofu . _.0)
         (_.0 tofu . _.1)
         (_.0 _.1 tofu . _.2)
         (_.0 _.1 _.2 tofu . _.3)
         (_.0 _.1 _.2 _.3 tofu . _.4)
         (_.0 _.1 _.2 _.3 _.4 tofu . _.5)
         (_.0 _.1 _.2 _.3 _.4 _.5 tofu . _.6)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 tofu . _.7)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 tofu . _.8)
         (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 tofu . _.9))))

  (letrec
    ((rembero
       (lambda (x l out)
         (conde
           ((nullo l) (== '() out))
           ((caro l x) (cdro l out))
           ((fresh (a d res)
              (conso a d l)
              (rembero x d res)
              (conso a res out)))))))

    (ftest "testc15.tex-17" 
      (run+ (out)
        (fresh (y)
          (rembero 'peas `(a b ,y d peas e) out)))
      `((a b d peas e)))

    (mtest "testc15.tex-18" 
      (run* (out)
        (fresh (y z)
          (rembero y `(a b ,y d ,z e) out)))
      `((b a d _.0 e)
        (a b d _.0 e)
        (a b d _.0 e)
        (a b d _.0 e)
        (a b _.0 d e)
        (a b e d _.0)
        (a b _.0 d _.1 e)))

    (mtest "testc15.tex-19" 
      (run* (r) 
        (fresh (y z) 
          (rembero y `(,y d ,z e) `(,y d e))
          (== `(,y ,z) r)))
      `((d d)
        (d d)
        (_.0 _.0)
        (e e)))

    (ftest "testc15.tex-20" 
      (run+ (w)
        (fresh (y z out)
          (rembero y `(a b ,y d ,z . ,w) out)))
      `(_.0 
         _.0
         _.0
         _.0
         _.0
         ()
         (_.0 . _.1)
         (_.0)
         (_.0 _.1 . _.2)
         (_.0 _.1)
         (_.0 _.1 _.2 . _.3)
         (_.0 _.1 _.2)
         (_.0 _.1 _.2 _.3 . _.4)))

    (let ((surpriseo
            (lambda (s)
              (rembero s '(a b c) '(a b c)))))

      (mtest "testc15.tex-21" 
        (run* (r)
          (== 'd r)
          (surpriseo r))
        (list 'd))

      (mtest "testc15.tex-22" 
        (run* (r)
          (surpriseo r))
        `(_.0))

      (mtest "testc15.tex-23" 
        (run* (r)
          (== 'b r)
          (surpriseo r))
        `(b))))

  (letrec
    ((appendo
       (lambda (l s out)
         (conde
           ((nullo l) (== s out))
           ((fresh (a d res)
              (caro l a)
              (cdro l d)   
              (appendo d s res)
              (conso a res out)))))))

    (mtest "testc16.tex-5" 
      (run* (x)
        (appendo
          '(cake)
          '(tastes yummy)
          x))
      (list `(cake tastes yummy)))

    (mtest "testc16.tex-6" 
      (run* (x)
        (fresh (y)
          (appendo
            `(cake with ice ,y)
            '(tastes yummy)
            x)))
      (list `(cake with ice _.0 tastes yummy)))

    (mtest "testc16.tex-7" 
      (run* (x)
        (fresh (y)
          (appendo
            '(cake with ice cream)
            y
            x)))
      (list `(cake with ice cream . _.0)))

    (ftest "testc16.tex-8" 
      (run+ (x)
        (fresh (y)
          (appendo `(cake with ice . ,y) '(d t) x)))
      (list `(cake with ice d t)))

    (ftest "testc16.tex-9" 
      (run+ (y)
        (fresh (x)
          (appendo `(cake with ice . ,y) '(d t) x)))
      (list '())))

(letrec
  ((appendo
     (lambda (l s out)
       (conde
         ((nullo l) (== s out))
         ((fresh (a d res)
            (conso a d l)
            (appendo d s res)
            (conso a res out)))))))

  (ftest "testc16.tex-10" 
    (run+ (x)
      (fresh (y)
        (appendo `(cake with ice . ,y) '(d t) x)))
    `((cake with ice d t)
      (cake with ice _.0 d t)
      (cake with ice _.0 _.1 d t)
      (cake with ice _.0 _.1 _.2 d t)
      (cake with ice _.0 _.1 _.2 _.3 d t)))

  (ftest "testc16.tex-11" 
    (run+ (y)
      (fresh (x)
        (appendo `(cake with ice . ,y) '(d t) x)))
    `(()
      (_.0)
      (_.0 _.1)
      (_.0 _.1 _.2)
      (_.0 _.1 _.2 _.3)))

  (ftest "testc16.tex-13" 
    (run+ (x)
      (fresh (y)
        (appendo
          `(cake with ice . ,y)
          `(d t . ,y)
          x)))
    `((cake with ice d t)
      (cake with ice _.0 d t _.0)
      (cake with ice _.0 _.1 d t _.0 _.1)
      (cake with ice _.0 _.1 _.2 d t _.0 _.1 _.2)
      (cake with ice _.0 _.1 _.2 _.3 d t _.0 _.1 _.2 _.3)))

  (mtest "testc16.tex-14" 
    (run* (x)
      (fresh (z)
        (appendo
          `(cake with ice cream)
          `(d t . ,z)
          x)))
    `((cake with ice cream d t . _.0)))

  (ftest "testc16.tex-15" 
    (run+ (x)
      (fresh (y)
        (appendo x y `(cake with ice d t))))
    `(()
      (cake)
      (cake with)
      (cake with ice)
      (cake with ice d)
      (cake with ice d t)))

  (ftest "testc16.tex-16" 
    (run+ (y)
      (fresh (x)
        (appendo x y `(cake with ice d t))))
    `((cake with ice d t)
      (with ice d t)
      (ice d t)
      (d t)
      (t)
      ()))

  (let ((appendxyquestion
        (lambda ()
          (run+ (r)
            (fresh (x y)
              (appendo x y `(cake with ice d t))
              (== `(,x ,y) r)))))
      (appendxyanswer
        `((() (cake with ice d t))
          ((cake) (with ice d t))
          ((cake with) (ice d t))
          ((cake with ice) (d t))
          ((cake with ice d) (t))
          ((cake with ice d t) ()))))
  (ftest "appendxy"
    (appendxyquestion)
    appendxyanswer)

  (dtest "testc16.tex-17" ;(skip "conj stops divergence?")
    (run 7 (r)
      (fresh (x y)
        (appendo x y `(cake with ice d t))
        (== `(,x ,y) r))))

  (letrec
    ((appendo
       (lambda (l s out)
         (conde
           ((nullo l) (== s out))
           ((fresh (a d res)
              (conso a d l)
              (conso a res out)
              (appendo d s res)))))))

    (mtest "testc16.tex-18" 
      (run 7 (r)
        (fresh (x y)
          (appendo x y `(cake with ice d t))
          (== `(,x ,y) r)))

      appendxyanswer)

    (ftest "testc16.tex-19" 
      (run+ (x)
        (fresh (y z)
          (appendo x y z)))
      `(()
        (_.0)
        (_.0 _.1)
        (_.0 _.1 _.2)
        (_.0 _.1 _.2 _.3)
        (_.0 _.1 _.2 _.3 _.4)
        (_.0 _.1 _.2 _.3 _.4 _.5)))

    (ftest "testc16.tex-20" 
      (run+ (y)
        (fresh (x z)
          (appendo x y z)))
      `(_.0 _.0 _.0 _.0 _.0 _.0  _.0))

    (ftest "testc16.tex-21" 
      (run+ (z)
        (fresh (x y)
          (appendo x y z)))
      `(_.0
         (_.0 . _.1)
         (_.0 _.1 . _.2)
         (_.0 _.1 _.2 . _.3)
         (_.0 _.1 _.2 _.3 . _.4)
         (_.0 _.1 _.2 _.3 _.4 . _.5)
         (_.0 _.1 _.2 _.3 _.4 _.5 . _.6)))

    (ftest "testc16.tex-22" 
      (run+ (r)
        (fresh (x y z)
          (appendo x y z)
          (== `(,x ,y ,z) r)))
      `((() _.0 _.0)
        ((_.0) _.1 (_.0 . _.1))
        ((_.0 _.1) _.2 (_.0 _.1 . _.2))
        ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
        ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))
        ((_.0 _.1 _.2 _.3 _.4) _.5 (_.0 _.1 _.2 _.3 _.4 . _.5))
        ((_.0 _.1 _.2 _.3 _.4 _.5) _.6 (_.0 _.1 _.2 _.3 _.4 _.5 . _.6))))))

  (letrec
    ((flatteno
       (lambda (s out)
         (conde
           ((nullo s) (== '() out))
           ((pairo s)
            (fresh (a d res-a res-d)
              (conso a d s)
              (flatteno a res-a)
              (flatteno d res-d)
              (appendo res-a res-d out)))
           ((conso s '() out))))))

    (ftest "testc16.tex-33" 
      (run+ (x)
        (flatteno '((a b) c) x))
      `((((a b) c))
        ((a b) (c))
        ((a b) c)
        (a (b) (c))
        ((a b) c ())
        (a (b) c)
        (a (b) c ())
        (a b (c))
        (a b () (c))
        (a b c)))

    (ftest "testc16.tex-34" 
      (run+ (x)
        (flatteno '(a (b c)) x))
      `(((a (b c)))
        (a ((b c)))
        (a (b c))
        (a (b c) ())
        (a b (c))
        (a b (c) ())
        (a b c)
        (a b c ())
        (a b c ())
        (a b c () ())))

    (mtest "testc16.tex-35" 
      (run* (x)
        (flatteno '(a) x))
      `(((a))
        (a)
        (a ())))

    (mtest "testc16.tex-36" 
      (run* (x)
        (flatteno '((a)) x))
      `((((a)))
        ((a))
        ((a) ())
        (a)
        (a ())
        (a ())
        (a () ())))

    (mtest "testc16.tex-37" 
      (run* (x)
        (flatteno '(((a))) x))
      `(((((a))))
        (((a)))
        (((a)) ())
        ((a))
        ((a) ())
        ((a) ())
        ((a) () ())
        (a)
        (a ())
        (a ())
        (a () ())
        (a ())
        (a () ())
        (a () ())
        (a () () ())))
    
    (let ((flattenogrumblequestion
            (lambda ()
              (run* (x)
                (flatteno '((a b) c) x))))
          (flattenogrumbleanswer
            `((((a b) c))
              ((a b) (c))
              ((a b) c)
              (a (b) (c))
              ((a b) c ())
              (a (b) c)
              (a (b) c ())
              (a b (c))
              (a b () (c))
              (a b c)
              (a b c ())
              (a b () c)
              (a b () c ()))))

      (mtest "flattenogrumble"
        (flattenogrumblequestion)
        flattenogrumbleanswer)

      (dtest "testc16.tex-38"
        (run* (x)
          (flatteno x '(a b c)))))
    
    (test "testc16.tex-39" 
      (length
        (run* (x)
          (flatteno '((((a (((b))) c))) d) x)))
      574)))

  (letrec
    ((swappendo
       (lambda (l s out)
         (conde
           ((fresh (a d res)
              (conso a d l)
              (conso a res out)
              (swappendo d s res)))
           ((nullo l) (== s out))))))

    (ftest "testc16.tex-23" 
      (run+ (r)
        (fresh (x y z)
          (swappendo x y z)
          (== `(,x ,y ,z) r)))
      `((() _.0 _.0)
        ((_.0) _.1 (_.0 . _.1))
        ((_.0 _.1) _.2 (_.0 _.1 . _.2))
        ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
        ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))
        ((_.0 _.1 _.2 _.3 _.4) _.5 (_.0 _.1 _.2 _.3 _.4 . _.5))
        ((_.0 _.1 _.2 _.3 _.4 _.5) _.6 (_.0 _.1 _.2 _.3 _.4 _.5 . _.6)))))

  (letrec
    ((unwrapo
       (lambda (x out)
         (conde
           ((pairo x)
            (fresh (a)
              (caro x a)
              (unwrapo a out)))
           ((== x out))))))

    (mtest "testc16.tex-26" 
      (run* (x)
        (unwrapo '(((pizza))) x))
      `((((pizza)))
        ((pizza))
        (pizza)
        pizza))

    (ftest "testc16.tex-27" 
      (run+ (x)
        (unwrapo x 'pizza))
      `(pizza))

    (ftest "testc16.tex-28" 
      (run+ (x)
        (unwrapo `((,x)) 'pizza))
      `(pizza))

    (ftest "testc16.tex-29" 
      (run+ (x)
        (unwrapo x 'pizza))
      `(pizza
         (pizza . _.0)
         ((pizza . _.0) . _.1)
         (((pizza . _.0) . _.1) . _.2)
         ((((pizza . _.0) . _.1) . _.2) . _.3)))

    (ftest "testc16.tex-30" 
      (run+ (x)
        (unwrapo x '((pizza))))
      `(((pizza))
        (((pizza)) . _.0)
        ((((pizza)) . _.0) . _.1)
        (((((pizza)) . _.0) . _.1) . _.2)
        ((((((pizza)) . _.0) . _.1) . _.2) . _.3)))

    (ftest "testc16.tex-31" 
      (run+ (x)
        (unwrapo `((,x)) 'pizza))
      `(pizza
         (pizza . _.0)
         ((pizza . _.0) . _.1)
         (((pizza . _.0) . _.1) . _.2)
         ((((pizza . _.0) . _.1) . _.2) . _.3))))

  (letrec ((strangeo (fresh () strangeo)))
    (dtest "testc17.tex-1"
      (run 1 (x) strangeo))

    (ftest "testc17.tex-2" 
      (run+ (q)
        (conde
          (strangeo)
          ((== #f #f))))
      `(_.0)))

  (letrec ((strangero
             (conde 
               (strangero (conde 
                            (strangero) 
                            ((== #f #f))))
               ((== #f #f)))))

    (ftest "testc17.tex-3" 
      (run+ (q) 
        strangero)
      `(_.0 _.0 _.0 _.0 _.0)))

  (letrec
    ((strangesto
       (lambda (x y)
         (conde
           ((strangesto y x) (== #f y))
           ((== #f x))))))

    (ftest "testc17.tex-4" 
      (run+ (q)
        (fresh (x y)
          (strangesto x y)
          (== `(,x ,y) q)))
      `((#f _.0) (_.0 #f) (#f #f) (#f #f) (#f #f))))

  (letrec
    ((any* (lambda (g)
             (conde
               (g)
               ((any* g)))))
     (nevert (tabled (x)
               (conde
                 ((== #f #t))
                 ((nevert x)))))
     (alwayst (tabled (x)
                (conde
                  ((== #f #f))
                  ((alwayst x))))))
    (let ((never (any* (== #t #f)))
          (always (any* (== #f #f))))

      (dtest "testc17.tex-5" 
        (run 1 (q)
          never 
          (== #t q)))

      (mtest "testc17.tex-5t" 
        (run* (q)
          (nevert q) 
          (== #t q))
        '())
      
      (ftest "testc17.tex-6"   
        (run+ (q) 
          always 
          (== #t q))
        (list #t))

      (mtest "testc17.tex-6t"
        (run* (q) 
          (alwayst q) 
          (== #t q))
        `(#t))
      
      (dtest "testc17.tex-7"
        (run* (q) 
          always 
          (== #t q)))

      (test "testc17.tex-8"   
        (run 5 (q) 
          always 
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-9"   
        (run 5 (q) 
          (== #t q) 
          always)
        `(#t #t #t #t #t))

      (let ((salo
              (lambda (g)
                (conde
                  ((== #f #f))
                  (g)))))

        (ftest "testc17.tex-10"   
          (run+ (q)
            (salo always)
            (== #t q))
          `(#t))

        (ftest "testc17.tex-11" 
          (run+ (q)
            (salo never)
            (== #t q))
          `(#t))

        (dtest "testc17.tex-12"
          (run* (q)
            (salo never)
            (== #t q)))

        (dtest "testc17.tex-13" ;(skip "conj stops divergence?")
          (run 1 (q)
            (salo never)
            (== #t #f)
            (== #t q)))

        (dtest "testc17.tex-14" ;(skip "conj stops divergence?")
          (run 1 (q) 
            always 
            (== #t #f)
            (== #t q))))

      (ftest "testc17.tex-15"   
        (run+ (q)
          (conde
            ((== #f q) always)
            ((== #t q)))
          (== #t q))
        `(#t))

      (dtest "testc17.tex-16" ;(skip "conj stops divergence?")
        (run 2 (q)
          (conde
            ((== #f q) always)
            ((== #t q)))
          (== #t q)))

      (test "testc17.tex-17"   
        (run 5 (q)
          (conde                                                                  
            ((== #f q) always)                                              
            ((any* (== #t q)))) 
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-18" 
        (run 5 (q)
          (conde
            (always)
            (never))
          (== #t q))
        `(#t #t #t #t #t))

      (ftest "testc17.tex-19"   
        (run+ (q)
          (fresh ()
            (conde
              ((== #f q))
              ((== #t q)))                    
            always)                                                        
          (== #t q))
        `(#t))

      (test "testc17.tex-20"   
        (run 5 (q)
          (fresh ()
            (conde
              ((== #f q))
              ((== #t q)))                    
            always)                                                        
          (== #t q))
        `(#t #t #t #t #t))

      (test "testc17.tex-21"   
        (run 5 (q)
          (fresh ()
            (conde
              ((== #t q))
              ((== #f q)))
            always)                                           
          (== #t q))
        `(#t #t #t #t #t))))
  (let
    ((bit-xoro
       (lambda (x y r)
         (conde
           ((== 0 x) (== 0 y) (== 0 r))
           ((== 0 x) (== 1 y) (== 1 r))
           ((== 1 x) (== 0 y) (== 1 r))
           ((== 1 x) (== 1 y) (== 0 r)))))
     (bit-ando
       (lambda (x y r)
         (conde
           ((== 0 x) (== 0 y) (== 0 r))
           ((== 1 x) (== 0 y) (== 0 r))
           ((== 0 x) (== 1 y) (== 0 r))
           ((== 1 x) (== 1 y) (== 1 r))))))

    (mtest "testc20.tex-1" 
      (run* (s)
        (fresh (x y)
          (bit-xoro x y 0)
          (== `(,x ,y) s)))  
      `((0 0)
        (1 1)))

    (mtest "testc20.tex-2" 
      (run* (s)
        (fresh (x y)
          (bit-xoro x y 1)
          (== `(,x ,y) s)))
      `((0 1)
        (1 0)))

    (mtest "testc20.tex-3" 
      (run* (s)
        (fresh (x y r)
          (bit-xoro x y r)
          (== `(,x ,y ,r) s)))
      `((0 0 0) 
        (0 1 1)
        (1 0 1)
        (1 1 0)))
    
  (mtest "testc20.tex-4" 
    (run* (s)
      (fresh (x y)
        (bit-ando x y 1)
        (== `(,x ,y) s)))  
    `((1 1)))

    (let
      ((half-addero
         (lambda (x y r c)
           (fresh ()
             (bit-xoro x y r)
             (bit-ando x y c)))))

      (mtest "testc20.tex-5" 
        (run* (r)
          (half-addero 1 1 r 1))
        (list 0))

      (mtest "testc20.tex-6" 
        (run* (s)
          (fresh (x y r c)
            (half-addero x y r c)
            (== `(,x ,y ,r ,c) s)))
        `((0 0 0 0)
          (0 1 1 0)
          (1 0 1 0)
          (1 1 0 1)))

      (let
        ((full-addero
           (lambda (b x y r c)
             (fresh (w xy wz)
               (half-addero x y w xy)
               (half-addero w b r wz)
               (bit-xoro xy wz c)))))

        (mtest "testc20.tex-7" 
          (run* (s)
            (fresh (r c)
              (full-addero 0 1 1 r c)
              (== `(,r ,c) s)))
          (list `(0 1))))))

  (let
    ((full-addero
       (lambda (b x y r c)
         (conde
           ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
           ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
           ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
           ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
           ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
           ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
           ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
           ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))))

    (mtest "testc20.tex-8" 
      (run* (s)
        (fresh (r c)
          (full-addero 1 1 1 r c)
          (== `(,r ,c) s)))
      (list `(1 1)))

    (mtest "testc20.tex-9" 
      (run* (s)
        (fresh (b x y r c)
          (full-addero b x y r c)
          (== `(,b ,x ,y ,r ,c) s)))
      `((0 0 0 0 0)
        (1 0 0 1 0)
        (0 1 0 1 0)
        (1 1 0 0 1)
        (0 0 1 1 0)
        (1 0 1 0 1)
        (0 1 1 0 1)
        (1 1 1 1 1)))
    
(let
  ((poso
     (lambda (n)
       (fresh (a d)
         (== `(,a . ,d) n)))))

  (mtest "testc20.tex-15" 
    (run* (q)
      (poso '(0 1 1))
      (== #t q))
    (list #t))

  (mtest "testc20.tex-16" 
    (run* (q)
      (poso '(1))
      (== #t q))
    (list #t))

  (mtest "testc20.tex-17" 
    (run* (q)
      (poso '())
      (== #t q))
    `())

  (mtest "testc20.tex-18" 
    (run* (r)
      (poso r))
    (list `(_.0 . _.1)))
  
  (let ((>1o
          (lambda (n)
            (fresh (a ad dd)
              (== `(,a ,ad . ,dd) n)))))

    (mtest "testc20.tex-19" 
      (run* (q)
        (>1o '(0 1 1))
        (== #t q))
      (list #t))

    (mtest "testc20.tex-20" 
      (run* (q)
        (>1o '(0 1))
        (== #t q))
      `(#t))

    (mtest "testc20.tex-21" 
      (run* (q)
        (>1o '(1))
        (== #t q))
      `())

    (mtest "testc20.tex-22" 
      (run* (q)
        (>1o '())
        (== #t q))
      `())

    (mtest "testc20.tex-23" 
      (run* (r)
        (>1o r))
      (list 
        `(_.0 _.1 . _.2)))
    
    (letrec
      ((addero
         (lambda (d n m r)
           (conde
             ((== 0 d) (== '() m) (== n r))
             ((== 0 d) (== '() n) (== m r)
              (poso m))
             ((== 1 d) (== '() m)
              (addero 0 n '(1) r))
             ((== 1 d) (== '() n) (poso m)
              (addero 0 '(1) m r))
             ((== '(1) n) (== '(1) m)
              (fresh (a c)
                (== `(,a ,c) r)
                (full-addero d 1 1 a c)))
             ((== '(1) n) (gen-addero d n m r))
             ((== '(1) m) (>1o n) (>1o r)
              (addero d '(1) n r))
             ((>1o n) (gen-addero d n m r)))))

       (gen-addero
         (lambda (d n m r)
           (fresh (a b c e x y z)
             (== `(,a . ,x) n)
             (== `(,b . ,y) m) (poso y)
             (== `(,c . ,z) r) (poso z)
             (full-addero d a b c e)
             (addero e x y z)))))

      (ftest "testc20.tex-24" 
        (run+ (s)
          (fresh (x y r)
            (addero 0 x y r)
            (== `(,x ,y ,r) s)))
        `((_.0 () _.0)
          (() (_.0 . _.1) (_.0 . _.1))
          ((1) (1) (0 1))))

      (ftest "testc20.tex-25"
        (run+ (s)
          (fresh (x y r)
            (addero 0 x y r)
            (== `(,x ,y ,r) s)))
        `((_.0 () _.0)
          (() (_.0 . _.1) (_.0 . _.1))
          ((1) (1) (0 1))
          ((1) (0 _.0 . _.1) (1 _.0 . _.1))
          ((1) (1 1) (0 0 1))
          ((0 _.0 . _.1) (1) (1 _.0 . _.1))
          ((1) (1 0 _.0 . _.1) (0 1 _.0 . _.1))
          ((0 1) (0 1) (0 0 1))
          ((1) (1 1 1) (0 0 0 1))
          ((1 1) (1) (0 0 1))
          ((1) (1 1 0 _.0 . _.1) (0 0 1 _.0 . _.1))
          ((1 1) (0 1) (1 0 1))
          ((1) (1 1 1 1) (0 0 0 0 1))
          ((1 0 _.0 . _.1) (1) (0 1 _.0 . _.1))
          ((1) (1 1 1 0 _.0 . _.1) (0 0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1) (0 0 0 0 0 1))
          ((1 1 1) (1) (0 0 0 1))
          ((1) (1 1 1 1 0 _.0 . _.1) (0 0 0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1 1) (0 0 0 0 0 0 1))
          ((0 1) (1 1) (1 0 1))
          ((1 1 0 _.0 . _.1) (1) (0 0 1 _.0 . _.1))
          ((1) (1 1 1 1 1 0 _.0 . _.1) (0 0 0 0 0 1 _.0 . _.1))))

      (mtest "testc20.tex-26" 
        (run* (s)
          (gen-addero 1 '(0 1 1) '(1 1) s))
        (list `(0 1 0 1)))

      (mtest "testc20.tex-27" 
        (run* (s)
          (fresh (x y)
            (addero 0 x y '(1 0 1))
            (== `(,x ,y) s)))
        `(((1 0 1) ())
          (() (1 0 1))
          ((1) (0 0 1))
          ((0 0 1) (1))
          ((1 1) (0 1))
          ((0 1) (1 1))))

      (let ((pluso (lambda (n m k) (addero 0 n m k))))
        (mtest "testc20.tex-28" 
          (run* (s)
            (fresh (x y)
              (pluso x y '(1 0 1))
              (== `(,x ,y) s)))
          `(((1 0 1) ())
            (() (1 0 1))
            ((1) (0 0 1))
            ((0 0 1) (1))
            ((1 1) (0 1))
            ((0 1) (1 1))))

        (let ((minuso (lambda (n m k) (pluso m k n))))
          (letrec ((bumpo
                     (lambda (n x)
                       (conde
                         ((== n x) (== #f #f))
                         ((fresh (m)
                            (minuso n '(1) m)
                            (bumpo m x)))))))
            (mtest "testc23.tex-18" 
              (run* (x)
                (bumpo '(1 1 1) x))
              `((1 1 1)
                (0 1 1)
                (1 0 1)
                (0 0 1)
                (1 1)
                (0 1)
                (1)
                ())))

          (mtest "testc20.tex-29" 
            (run* (q)
              (minuso '(0 0 0 1) '(1 0 1) q))
            `((1 1)))

          (mtest "testc20.tex-30" 
            (run* (q)
              (minuso '(0 1 1) '(0 1 1) q))
            `(()))

          (mtest "testc20.tex-31" 
            (run* (q)
              (minuso '(0 1 1) '(0 0 0 1) q))
            `())
          
          (letrec
            ((*o (lambda (n m p)
                   (conde
                     ((== '() n) (== '() p))
                     ((poso n) (== '() m) (== '() p))  
                     ((== '(1) n) (poso m) (== m p))   
                     ((>1o n) (== '(1) m) (== n p))
                     ((fresh (x z)
                        (== `(0 . ,x) n) (poso x)
                        (== `(0 . ,z) p) (poso z)
                        (>1o m)
                        (*o x m z)))
                     ((fresh (x y)
                        (== `(1 . ,x) n) (poso x)
                        (== `(0 . ,y) m) (poso y)
                        (*o m n p)))
                     ((fresh (x y)
                        (== `(1 . ,x) n) (poso x)      
                        (== `(1 . ,y) m) (poso y)
                        (odd-*o x n m p))))))

             (odd-*o
               (lambda (x n m p)
                 (fresh (q)
                   (bound-*o q p n m)
                   (*o x m q)
                   (pluso `(0 . ,q) m p))))

             (bound-*o
               (lambda (q p n m)
                 (== #f #f))))

            (dtest "testc21.tex-4"
              (run 2 (t)
                (fresh (n m)
                  (*o n m '(1))
                  (== `(,n ,m) t)))))

          (letrec
            ((*o
               (lambda (n m p)
                 (conde
                   ((== '() n) (== '() p))
                   ((poso n) (== '() m) (== '() p))  
                   ((== '(1) n) (poso m) (== m p))   
                   ((>1o n) (== '(1) m) (== n p))
                   ((fresh (x z)
                      (== `(0 . ,x) n) (poso x)
                      (== `(0 . ,z) p) (poso z)
                      (>1o m)
                      (*o x m z)))
                   ((fresh (x y)
                      (== `(1 . ,x) n) (poso x)
                      (== `(0 . ,y) m) (poso y)
                      (*o m n p)))
                   ((fresh (x y)
                      (== `(1 . ,x) n) (poso x)      
                      (== `(1 . ,y) m) (poso y)
                      (odd-*o x n m p))))))

             (odd-*o
               (lambda (x n m p)
                 (fresh (q)
                   (bound-*o q p n m)
                   (*o x m q)
                   (pluso `(0 . ,q) m p))))

             (bound-*o
               (lambda (q p n m)
                 (conde
                   ((nullo q) (pairo p))
                   ((fresh (x y z)
                      (cdro q x)
                      (cdro p y)
                      (conde
                        ((nullo n)
                         (cdro m z)
                         (bound-*o x y z '()))
                        ((cdro n z) 
                         (bound-*o x y z m)))))))))


            (ftest "testc21.tex-1" 
              (run+ (t)
                (fresh (x y r)
                  (*o x y r)
                  (== `(,x ,y ,r) t)))
              `((() _.0 ())
                ((_.0 . _.1) () ())
                ((1) (_.0 . _.1) (_.0 . _.1))
                ((_.0 _.1 . _.2) (1) (_.0 _.1 . _.2))
                ((0 1) (_.0 _.1 . _.2) (0 _.0 _.1 . _.2))
                ((0 0 1) (_.0 _.1 . _.2) (0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 1) (0 1 _.0 . _.1))
                ((0 0 0 1) (_.0 _.1 . _.2) (0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 1) (0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 1) (0 0 1 _.0 . _.1))
                ((0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 1) (0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 1) (0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 1) (0 0 0 1 _.0 . _.1))
                ((1 1) (1 1) (1 0 0 1))
                ((0 0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 0 1) (0 0 0 0 1 _.0 . _.1))
                ((0 0 0 1 _.0 . _.1) (0 1) (0 0 0 0 1 _.0 . _.1))
                ((1 1) (1 0 1) (1 1 1 1))
                ((0 1 1) (1 1) (0 1 0 0 1))
                ((1 1) (1 1 1) (1 0 1 0 1))
                ((1 1) (0 1 1) (0 1 0 0 1))
                ((0 0 0 0 0 0 1) (_.0 _.1 . _.2) (0 0 0 0 0 0 _.0 _.1 . _.2))
                ((1 _.0 . _.1) (0 0 0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 1 _.0 . _.1) (0 0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 0 1 _.0 . _.1) (0 0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 0 0 1 _.0 . _.1) (0 0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((1 0 1) (1 1) (1 1 1 1))
                ((0 0 0 0 1 _.0 . _.1) (0 1) (0 0 0 0 0 1 _.0 . _.1))
                ((0 1 1) (1 0 1) (0 1 1 1 1))
                ((0 0 1 1) (1 1) (0 0 1 0 0 1))
                ((1 1) (1 0 0 1) (1 1 0 1 1))))

            (mtest "testc21.tex-2" 
              (run* (p)
                (*o '(0 1) '(0 0 1) p))  
              (list `(0 0 0 1)))

            (ftest "testc21.tex-3" 
              (run+ (t)
                (fresh (n m)
                  (*o n m '(1))
                  (== `(,n ,m) t)))
              (list `((1) (1))))
            
            (mtest "testc21.tex-6" ;(skip "*o looping")
              (run* (p)
                (*o '(1 1 1) '(1 1 1 1 1 1) p))
              (list `(1 0 0 1 1 1 0 1 1)))

            (letrec
              ((=lo
                 (lambda (n m)
                   (conde
                     ((== '() n) (== '() m))
                     ((== '(1) n) (== '(1) m))
                     ((fresh (a x b y)
                        (== `(,a . ,x) n) (poso x)
                        (== `(,b . ,y) m) (poso y)
                        (=lo x y)))))))

              (mtest "testc21.tex-7" 
                (run* (t)
                  (fresh (w x y)
                    (=lo `(1 ,w ,x . ,y) '(0 1 1 0 1))
                    (== `(,w ,x ,y) t)))
                (list `(_.0 _.1 (_.2 1))))

              (mtest "testc21.tex-8" 
                (run* (b)
                  (=lo '(1) `(,b)))
                (list 1))

              (mtest "testc21.tex-9" 
                (run* (n)
                  (=lo `(1 0 1 . ,n) '(0 1 1 0 1)))
                (list `(_.0 1)))

              (ftest "testc21.tex-10" 
                (run+ (t)
                  (fresh (y z)
                    (=lo `(1 . ,y) `(1 . ,z))
                    (== `(,y ,z) t)))
                `((() ())
                  ((1) (1))
                  ((_.0 1) (_.1 1))
                  ((_.0 _.1 1) (_.2 _.3 1))
                  ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))))

              (ftest "testc21.tex-11" 
                (run+ (t)
                  (fresh (y z)
                    (=lo `(1 . ,y) `(0 . ,z))
                    (== `(,y ,z) t)))
                `(((1) (1))
                  ((_.0 1) (_.1 1))
                  ((_.0 _.1 1) (_.2 _.3 1))
                  ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))
                  ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 1))))

              (ftest "testc21.tex-12" 
                (run+ (t)
                  (fresh (y z)
                    (=lo `(1 . ,y) `(0 1 1 0 1 . ,z))
                    (== `(,y ,z) t)))
                `(((_.0 _.1 _.2 1) ())
                  ((_.0 _.1 _.2 _.3 1) (1))
                  ((_.0 _.1 _.2 _.3 _.4 1) (_.5 1))
                  ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 1))
                  ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 1) (_.7 _.8 _.9 1))))

              (letrec ((<lo
                         (lambda (n m)
                           (conde
                             ((== '() n) (poso m))
                             ((== '(1) n) (>1o m))
                             ((fresh (a x b y)
                                (== `(,a . ,x) n) (poso x)
                                (== `(,b . ,y) m) (poso y)
                                (<lo x y)))))))

                (ftest "testc21.tex-13" 
                  (run+ (t)
                    (fresh (y z)
                      (<lo `(1 . ,y) `(0 1 1 0 1 . ,z))
                      (== `(,y ,z) t)))
                  `((() _.0)
                    ((1) _.0)
                    ((_.0 1) _.1)
                    ((_.0 _.1 1) _.2)
                    ((_.0 _.1 _.2 1) (_.3 . _.4))
                    ((_.0 _.1 _.2 _.3 1) (_.4 _.5 . _.6))
                    ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 . _.8))
                    ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 _.8 _.9 . _.10))))

                (dtest "testc21.tex-14"
                  (run 1 (n)
                    (<lo n n)))

                (let ((<=lo
                        (lambda (n m)
                          (conde
                            ((=lo n m))
                            ((<lo n m))))))

                  (ftest "testc21.tex-15" 
                    (run+ (t)
                      (fresh (n m)
                        (<=lo n m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (1))
                      (() (_.0 . _.1))
                      ((1) (_.0 _.1 . _.2))
                      ((_.0 1) (_.1 1))
                      ((_.0 1) (_.1 _.2 _.3 . _.4))
                      ((_.0 _.1 1) (_.2 _.3 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))))

                  (ftest "testc21.tex-16" 
                    (run+ (t)
                      (fresh (n m)
                        (<=lo n m)
                        (*o n '(0 1) m)
                        (== `(,n ,m) t)))
                    (list `(() ())))

                  (ftest "testc21.tex-17" 
                    (run+ (t)
                      (fresh (n m)
                        (<=lo n m)
                        (*o n '(0 1) m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (0 1))
                      ((0 1) (0 0 1))
                      ((1 1) (0 1 1))
                      ((1 _.0 1) (0 1 _.0 1))
                      ((0 0 1) (0 0 0 1))
                      ((0 1 1) (0 0 1 1))
                      ((1 _.0 _.1 1) (0 1 _.0 _.1 1))
                      ((0 1 _.0 1) (0 0 1 _.0 1))
                      ((0 0 0 1) (0 0 0 0 1))))

                  (ftest "testc21.tex-18" 
                    (run+ (t)
                      (fresh (n m)
                        (<=lo n m)
                        (== `(,n ,m) t)))
                    `((() ())
                      ((1) (1))
                      (() (_.0 . _.1))
                      ((1) (_.0 _.1 . _.2))
                      ((_.0 1) (_.1 1))
                      ((_.0 1) (_.1 _.2 _.3 . _.4))
                      ((_.0 _.1 1) (_.2 _.3 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 1))
                      ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . _.6))
                      ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 1))
                      ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . _.8))
                      ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 _.8 _.9 1))
                      ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . _.10))
                      ((_.0 _.1 _.2 _.3 _.4 _.5 1) (_.6 _.7 _.8 _.9 _.10 _.11 1))
                      ((_.0 _.1 _.2 _.3 _.4 1) (_.5 _.6 _.7 _.8 _.9 _.10 _.11 . _.12))))
                  
                (letrec ((<o
                           (lambda (n m)
                             (conde
                               ((<lo n m))
                               ((=lo n m)
                                (fresh (x)
                                  (poso x)
                                  (pluso n x m))))))
                         
                         (<=o
                           (lambda (n m)
                             (conde
                               ((== n m))
                               ((<o n m))))))

                  (mtest "testc21.tex-19" 
                    (run* (q)
                      (<o '(1 0 1) '(1 1 1))
                      (== #t q))
                    (list #t))

                  (mtest "testc21.tex-20" 
                    (run* (q)
                      (<o '(1 1 1) '(1 0 1))
                      (== #t q))
                    `())

                  (mtest "testc21.tex-21" 
                    (run* (q)
                      (<o '(1 0 1) '(1 0 1))
                      (== #t q))
                    `())

                  (mtest "lessthanequalo-1"
                    (run* (q)
                      (<=o '(1 0 1) '(1 0 1))
                      (== #t q))
                    `(#t))

                  (mtest "testc21.tex-22" 
                    (run* (n)
                      (<o n `(1 0 1)))
                    `(() (1) (_.0 1) (0 0 1)))

                  (mtest "testc21.tex-23"
                    (run* (m)
                      (<o `(1 0 1) m))
                    `((_.0 _.1 _.2 _.3 . _.4) (0 1 1) (1 1 1)))

                  (dtest "testc21.tex-24"
                    (run* (n)
                      (<o n n)))

                  (letrec ((/o
                    (lambda (n m q r)
                      (conde
                        ((== '() q) (== n r) (<o n m))
                        ((== '(1) q) (== '() r) (== n m)
                         (<o r m))      
                        ((<o m n) (<o r m)
                         (fresh (mq)
                           (<=lo mq n)
                           (*o m q mq)
                           (pluso mq r n))))))

                           (/otest1
                             (lambda ()
                               (run 3 (t)
                                 (fresh (y z)
                                   (/o `(1 0 . ,y) '(0 1) z '())
                                   (== `(,y ,z) t))))))
                    (dtest "testc23.tex-/otest1"
                      (/otest1)))

                  (letrec
                    ((/o
                       (lambda (n m q r)
                         (conde
                           ((== r n) (== '() q) (<o n m))
                           ((== '(1) q) (=lo n m) (pluso r m n)
                            (<o r m))
                           ((<lo m n)                        
                            (<o r m)                        
                            (poso q)                 
                            (fresh (nh nl qh ql qlm qlmr rr rh)
                              (splito n r nl nh)
                              (splito q r ql qh)
                              (conde
                                ((== '() nh)
                                 (== '() qh)
                                 (minuso nl r qlm)
                                 (*o ql m qlm))
                                ((poso nh)
                                 (*o ql m qlm)
                                 (pluso qlm r qlmr)
                                 (minuso qlmr nl rr)
                                 (splito rr r '() rh)
                                 (/o nh m qh rh))))))))

                     (splito
                       (lambda (n r l h)
                         (conde
                           ((== '() n) (== '() h) (== '() l))
                           ((fresh (b n^)
                              (== `(0 ,b . ,n^) n)
                              (== '() r)
                              (== `(,b . ,n^) h)
                              (== '() l)))
                           ((fresh (n^)
                              (==  `(1 . ,n^) n)
                              (== '() r)
                              (== n^ h)
                              (== '(1) l)))
                           ((fresh (b n^ a r^)
                              (== `(0 ,b . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== '() l)
                              (splito `(,b . ,n^) r^ '() h)))
                           ((fresh (n^ a r^)
                              (== `(1 . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== '(1) l)
                              (splito n^ r^ '() h)))
                           ((fresh (b n^ a r^ l^)
                              (== `(,b . ,n^) n)
                              (== `(,a . ,r^) r)
                              (== `(,b . ,l^) l)
                              (poso l^)
                              (splito n^ r^ l^ h)))))))

                    (ftest "testc21.tex-25" 
                      (run+ (t)
                        (fresh (n m q r)
                          (/o n m q r)
                          (== `(,n ,m ,q ,r) t)))
                      `((() (_.0 . _.1) () ())
                        ((1) (_.0 _.1 . _.2) () (1))
                        ((_.0 1) (_.1 _.2 _.3 . _.4) () (_.0 1))
                        ((_.0 _.1 1) (_.2 _.3 _.4 _.5 . _.6) () (_.0 _.1 1))
                        ((_.0 _.1 _.2 1) (_.3 _.4 _.5 _.6 _.7 . _.8) () (_.0 _.1 _.2 1))
                        ((_.0 _.1 _.2 _.3 1) (_.4 _.5 _.6 _.7 _.8 _.9 . _.10) () (_.0 _.1 _.2 _.3 1))))

                    (letrec
                      ((appendo
                         (lambda (l s out)
                           (conde
                             ((nullo l) (== s out))
                             ((fresh (a d res)
                                (conso a d l)
                                (conso a res out)
                                (appendo d s res))))))
                       (logo
                         (lambda (n b q r)
                           (conde
                             ((== '(1) n) (poso b) (== '() q) (== '() r))
                             ((== '() q) (<o n b) (pluso r '(1) n))
                             ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                             ((== '(1) b) (poso q) (pluso r '(1) n))
                             ((== '() b) (poso q) (== r n))
                             ((== '(0 1) b)
                              (fresh (a ad dd)
                                (poso dd)
                                (== `(,a ,ad . ,dd) n)
                                (exp2 n '() q)
                                (fresh (s)
                                  (splito n dd r s))))
                             ((fresh (a ad add ddd)
                                (conde
                                  ((== '(1 1) b))
                                  ((== `(,a ,ad ,add . ,ddd) b))))
                              (<lo b n)
                              (fresh (bw1 bw nw nw1 ql1 ql s)
                                (exp2 b '() bw1)
                                (pluso bw1 '(1) bw)
                                (<lo q n)
                                (fresh (q1 bwq1)
                                  (pluso q '(1) q1)
                                  (*o bw q1 bwq1)
                                  (<o nw1 bwq1))
                                (exp2 n '() nw1)
                                (pluso nw1 '(1) nw)
                                (/o nw bw ql1 s)
                                (pluso ql '(1) ql1)
                                (<=lo ql q)
                                (fresh (bql qh s qdh qd)
                                  (repeated-mul b ql bql)
                                  (/o nw bw1 qh s)
                                  (pluso ql qdh qh)
                                  (pluso ql qd q)
                                  (<=o qd qdh)
                                  (fresh (bqd bq1 bq)
                                    (repeated-mul b qd bqd)
                                    (*o bql bqd bq)
                                    (*o b bq bq1)
                                    (pluso bq r n)
                                    (<o n bq1))))))))

                       (exp2
                         (lambda (n b q)
                           (conde
                             ((== '(1) n) (== '() q))
                             ((>1o n) (== '(1) q)
                              (fresh (s)
                                (splito n b s '(1))))
                             ((fresh (q1 b2)
                                (== `(0 . ,q1) q)
                                (poso q1)
                                (<lo b n)
                                (appendo b `(1 . ,b) b2)
                                (exp2 n b2 q1)))
                             ((fresh (q1 nh b2 s)
                                (== `(1 . ,q1) q)
                                (poso q1)
                                (poso nh)
                                (splito n b s nh)
                                (appendo b `(1 . ,b) b2)
                                (exp2 nh b2 q1))))))

                       (repeated-mul
                         (lambda (n q nq)
                           (conde
                             ((poso n) (== '() q) (== '(1) nq))
                             ((== '(1) q) (== n nq))
                             ((>1o q)
                              (fresh (q1 nq1)
                                (pluso q1 '(1) q)
                                (repeated-mul n q1 nq1)
                                (*o nq1 n nq)))))))

                      (mtest "testc21.tex-26" 
                        (run* (r) 
                          (logo '(0 1 1 1) '(0 1) '(1 1) r))
                        (list `(0 1 1)))
                      
;;                       (ftest "testc21.tex-27"
;;                         (run+ (s)
;;                           (fresh (b q r)
;;                             (logo '(0 0 1 0 0 0 1) b q r)
;;                             (>1o q)
;;                             (== `(,b ,q ,r) s)))
;;                         `((() (_.0 _.1 . _.2) (0 0 1 0 0 0 1))
;;                           ((1) (_.0  _.1 . _.2) (1 1 0 0 0 0 1))
;;                           ((0 1) (0 1 1) (0 0 1))
;;                           ((1 1) (1 1) (1 0 0 1 0 1))
;;                           ((0 0 1) (1 1) (0 0 1))
;;                           ((0 0 0 1) (0 1) (0 0 1))
;;                           ((1 0 1) (0 1) (1 1 0 1 0 1))
;;                           ((0 1 1) (0 1) (0 0 0 0 0 1))
;;                           ((1 1 1) (0 1) (1 1 0 0 1))))

;;                       (let ((expo (lambda (b q n)
;;                                     (logo n b q '()))))
;;                         (mtest "testc21.tex-28"
;;                           (run* (t)
;;                             (expo '(1 1) '(1 0 1) t))
;;                           (list `(1 1 0 0 1 1 1 1))))
                      
                      )))))))))))))))))))

(letrec ((proof-that-exist-needs-an-inc
           (fresh ()
             (proof-that-exist-needs-an-inc))))
  (mtest 'proof-that-run-needs-an-inc
    (run 1 (q)
      (conde
        (proof-that-exist-needs-an-inc)
        ((== #f #f))))
    '(_.0))

  (mtest 'proof-that-run-needs-an-inc-with-conde
    (run 1 (q)
      (conde
        (proof-that-exist-needs-an-inc (== #f #f))
        ((== #f #f))))
    '(_.0)))

(mtest 'why-conde-must-also-have-an-inc
  (run 5 (q) 
    (letrec ((f (fresh () 
                  (conde 
                    (f (conde 
                         (f) 
                         ((== #f #f)))) 
                    ((== #f #f)))))) 
      f))
  '(_.0 _.0 _.0 _.0 _.0))

;; (test "testc22.tex-19" 
;;   (run* (q)
;;     (== #f q)
;;     (project (q)
;;       (== (not (not q)) q)))
;;   '(#f))

(dtest "testc22.tex-25"
  (run 1 (x)
    (==-no-check `(,x) x)))

(mtest "testc22.tex-26"   
  (run* (q) 
    (fresh (x)
      (==-no-check `(,x) x)
      (== #t q)))
  `(#t))

;;; violates occurs check
(mtest "testc22.tex-27"   
  (run* (q)
    (fresh (x y)
      (== `(,x) y)
      (== `(,y) x)
      (== #t q)))
  `())

(test "testc22.tex-28"   
  (run 1 (x) 
    (== `(,x) x))
  `())

(dtest "testc22.tex-29"
  (run 1 (x)
    (fresh (y z)
      (== x z)
      (== `(a b ,z) y)
      (==-no-check x y))))

(test "testc22.tex-30" 
  (run 1 (x)
    (fresh (y z)
      (== x z)
      (== `(a b ,z) y)
      (== x y)))
  `())


(ftest "farmer no tabling"
  (letrec
    ((state
       (lambda (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (fresh (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (lambda (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (lambda (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FC FG FW FF FG)))

(ftest "farmer tabled state only"
  (letrec
    ((state
       (tabled (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (fresh (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (lambda (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (lambda (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FC FG FW FF FG)))

(ftest "farmer"
  (letrec
    ((state
       (tabled (farmer wolf goat cabbage path)
         (conde
           ((== farmer 'north)
            (== wolf 'north)
            (== goat 'north)
            (== cabbage 'north)
            (== path '()))
           ((== farmer wolf)
            (safe farmer wolf goat cabbage)
            (fresh (newpath crossed)
              (== path `(FW . ,newpath))
              (opposite farmer crossed)
              (state crossed crossed goat cabbage newpath)))
           ((== farmer goat)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FG . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf crossed cabbage newpath)))
           ((== farmer cabbage)
            (safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FC . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat crossed newpath)))
           ((safe farmer wolf goat cabbage)
            (fresh (crossed newpath)
              (== path `(FF . ,newpath))
              (opposite farmer crossed)
              (state crossed wolf goat cabbage newpath))))))
     (opposite
       (tabled (s1 s2)
         (conde
           ((== s1 'north) (== s2 'south))
           ((== s1 'south) (== s2 'north)))))
     (safe
       (tabled (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (state 'south 'south 'south 'south q)))
  '((FG FF FW FG FC FF FG) (FG FF FC FG FW FF FG)))

(ftest "alternative farmer" 
  (letrec
    ((valid
       (tabled (farmer wolf goat cabbage path)
         (safe farmer wolf goat cabbage)
         (conde
           ((== `(,farmer ,wolf ,goat ,cabbage) '(north north north north))
            (== path '()))
           ((fresh (which new-farmer new-wolf new-goat new-cabbage new-path)
              (== path `(,which . ,new-path))
              (opposite farmer new-farmer)
              (one-with farmer new-farmer which
                `((FW ,wolf ,new-wolf)
                  (FG ,goat ,new-goat)
                  (FC ,cabbage ,new-cabbage)))
              (valid new-farmer new-wolf new-goat new-cabbage new-path))))))
     (one-with
       (tabled (oldf newf which choices)
         (conde
           ((== choices '()) (== which 'FF))
           ((fresh (choice rest)
              (== choices `(,choice . ,rest))
              (conde
                ((== choice `(,which ,oldf ,newf)) (stay rest))
                ((stay `(,choice)) (one-with oldf newf which rest))))))))
     (stay
       (tabled (choices)
         (conde
           ((== choices '()))
           ((fresh (tag pos rest)
              (== choices `((,tag ,pos ,pos) . ,rest))
              (stay rest))))))
     (opposite
       (tabled (pos1 pos2)
         (conde
           ((== pos1 'north) (== pos2 'south))
           ((== pos1 'south) (== pos2 'north)))))
     (safe
       (tabled (farmer wolf goat cabbage)
         (conde
           ((== farmer goat))
           ((== farmer wolf)
            (== farmer cabbage)
            (opposite farmer goat))))))
    (run+ (q) (valid 'south 'south 'south 'south q)))
  '((FG FF FW FG FC FF FG) (FG FF FC FG FW FF FG)))

(print "DONE" nl "SKIPPED: " (skipped-tests) nl) #!eof

I think everything below is testing unexported/non-declarative features.

(define gen&testo
  (lambda (op i j k)
    (onceo
      (fresh (x y z)
        (op x y z)
        (== i x)
        (== j y)
        (== k z)))))

(test-check "testc23.tex-19" 
(run* (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(1 1 1))
  (== #t q))

(list 
#t
))
(define e (make-engine (lambda () 
(run1 (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(0 1 1)))
)))
(printf "Testing testc23.tex-20  (engine with ~s ticks fuel)\n" max-ticks)
(e max-ticks
(lambda (t v) (error 'testc23.tex-20 "infinite loop returned ~s after ~s ticks" v (- max-ticks t)))
(lambda (e^) (void)))

(define e (make-engine (lambda () 
(run1 (q)
  (gen&testo pluso '(0 0 1) '(1 1) '(0 1 1)))
)))
(printf "Testing testc23.tex-21  (engine with ~s ticks fuel)\n" max-ticks)
(e max-ticks
(lambda (t v) (error 'testc23.tex-21 "infinite loop returned ~s after ~s ticks" v (- max-ticks t)))
(lambda (e^) (void)))


(define enumerateo
  (lambda (op r n)
    (fresh (i j k)
      (bumpo n i)
      (bumpo n j)
      (op i j k)
      (gen&testo op i j k)
      (== `(,i ,j ,k) r))))


(test-check "testc23.tex-22" 
(run* (s)
  (enumerateo pluso s '(1 1)))


`(((1 1) (1 1) (0 1 1))
 ((1 1) (0 1) (1 0 1))
 ((1 1) () (1 1))
 ((0 1) (1 1) (1 0 1))
 ((1 1) (1) (0 0 1))
 ((1) (1 1) (0 0 1))
 ((0 1) (0 1) (0 0 1))
 (() (1 1) (1 1))
 ((0 1) () (0 1))
 ((0 1) (1) (1 1))
 ((1) (0 1) (1 1))
 ((1) (1) (0 1))
 ((1) () (1))
 (() (0 1) (0 1))
 (() (1) (1))
 (() () ()))
)

(run* (s)
  (enumerateo pluso s '(1 1)))


(test-check "testc23.tex-23" 
(run1 (s)
  (enumerateo pluso s '(1 1 1)))


`(((1 1 1) (1 1 1) (0 1 1 1)))
)

(test-check "testc22.tex-4" 
(walk z `((,z . a) (,x . ,w) (,y . ,z)))
'a)

(test-check "testc22.tex-5"   
(walk y `((,z . a) (,x . ,w) (,y . ,z)))
'a)

(test-check "testc22.tex-6"   
(walk x `((,z . a) (,x . ,w) (,y . ,z)))
w)

(test-check "testc22.tex-7"   
(walk w `((,z . a) (,x . ,w) (,y . ,z)))
w)

(test-check "testc22.tex-8"   
(walk u `((,x . b) (,w . (,x e ,x)) (,u . ,w)))
`(,x e ,x))


(test-check "testc22.tex-9" 
(walk y (ext-s x 'e `((,z . ,x) (,y . ,z))))
'e)

(test-check "testc22.tex-10"                                                    
(walk y `((,x . e)))                                                            
y)

(test-check "testc22.tex-11"   
(walk x `((,y . ,z) (,x . ,y)))
z)

(test-check "testc22.tex-12"   
(walk x (ext-s y z `((,x . ,y))))
z)

(test-check "testc22.tex-13" 
(walk x (ext-s z 'b `((,y . ,z) (,x . ,y))))
'b)

(test-check "testc22.tex-14" 
(walk x (ext-s z w `((,y . ,z) (,x . ,y))))
w)


(test-check "testc22.tex-15" 
(occurs-check z u 
  `((,x . (a ,y)) (,w . (,x e ,x)) (,u . ,w) (,y . (,z))))
#t)

(test-check "testc22.tex-16"   
(walk* x
  `((,y . (a ,z c)) (,x . ,y) (,z . a)))
`(a a c))

(test-check "testc22.tex-17" 
(walk* x
  `((,y . (,z ,w c)) (,x . ,y) (,z . a)))
`(a ,w c))

(test-check "testc22.tex-18" 
(walk* y
  `((,y . (,w ,z c)) (,v . b) (,x . ,v) (,z . ,x)))
`(,w b c))

(test-check "testc22.tex-20" 
(let ((r (walk* `(,x ,y ,z) empty-s)))
  (walk* r (reify-s r empty-s)))
`(_.0 _.1 _.2))

(test-check "testc22.tex-21" 
(let ((r `(,u (,v (,w ,x) ,y) ,x)))
  (walk* r (reify-s r empty-s)))
`(_.0 (_.1 (_.2 _.3) _.4) _.3))

(test-check "testc22.tex-22" 
(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . a))))
  (let ((r (walk* x s)))
    (walk* r (reify-s r empty-s))))
`(a _.0 c _.0))

(test-check "testc22.tex-23" 
(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . ,u))))
  (let ((r (walk* x s)))
    (walk* r (reify-s r empty-s))))
`(_.0 _.1 c _.1))

;(test-check "testc22.tex-24" 
;(let ((s `((,y . (,z ,w c ,w)) (,x . ,y) (,z . a))))
;  (reify x s))
;`(a _.0 c _.0))
(define proof-that-exist-needs-an-inc-with-conda
  (conda
    (proof-that-exist-needs-an-inc)))

(test-check 'proof-that-run-needs-an-inc-with-conde-and-conda
  (run 1 (q)
    (conde
      (proof-that-exist-needs-an-inc)
      ((== #f #f))))
  '(_.0))

(define proof-that-exist-needs-an-inc-with-conda
  (fresh ()
    (conda
      (proof-that-exist-needs-an-inc (== #f #f)))))
