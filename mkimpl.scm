;;; code from mkimpl.scm

(define-syntax lambdag@
  (syntax-rules ()
    ((_ (p) e) (lambda (p) e))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define-syntax rhs
  (syntax-rules ()
    ((_ x) (cdr x))))

(define-syntax lhs
  (syntax-rules ()
    ((_ x) (car x))))


(define-syntax mzero 
  (syntax-rules () 
    ((_) #f)))

(define-syntax unit
  (syntax-rules ()
    ((_ a) a)))

(define-syntax choice
  (syntax-rules ()
    ((_ a f) (cons a f))))

(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector x))))

(define-syntax var?
  (syntax-rules ()
    ((_ x) (vector? x))))

(define empty-s '())

(define ext-s
  (lambda (x v s)                                                              
    (cond                                                                       
      ((occurs-check x v s) #f)                                                 
      (else (ext-s-no-check x v s)))))

(define ext-s-no-check
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (rhs a) s))
           (else v))))
      (else v))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) (or (occurs-check x (car v) s) (occurs-check x (cdr v) s)))
        (else #f)))))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) 
         (cond
           ((var? v) (ext-s-no-check u v s))
           (else (ext-s u v s))))
        ((var? v) (ext-s v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s (unify (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define unify-no-check
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) s)
        ((var? u) (ext-s-no-check u v s))
        ((var? v) (ext-s-no-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify-no-check (car u) (car v) s)))
           (and s (unify-no-check (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define walk*
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) v)
        ((pair? v) (cons (walk* (car v) s) (walk* (cdr v) s)))
        (else v)))))

;; (define reify
;;   (lambda (v s)
;;     (let ((v (walk* v s)))
;;       (walk* v (reify-s v empty-s)))))

;; (define reify-s
;;   (lambda (v s)
;;     (let ((v (walk v s)))
;;       (cond
;;         ((var? v) (ext-s-no-check v (reify-name (length s)) s))
;;         ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
;;         (else s)))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

;; (define-syntax case-inf
;;   (syntax-rules ()
;;     ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
;;      (let ((a-inf e))
;;        (cond
;;          ((not a-inf) e0)
;;          ((procedure? a-inf)  (let ((f^ a-inf)) e1))
;;          ((and (pair? a-inf) (procedure? (cdr a-inf)))
;;           (let ((a (car a-inf)) (f (cdr a-inf))) e3))
;;          (else (let ((a^ a-inf)) e2)))))))

(define-syntax ==
  (syntax-rules ()
    ((_ u v) 
     (lambdag@ (a)
       (cond
         ((unify u v a) => (lambda (a) (unit a)))
         (else (mzero)))))))

(define-syntax ==-no-check
  (syntax-rules ()
    ((_ u v)
     (lambdag@ (a)
       (cond
         ((unify-no-check u v a) => (lambda (a) (unit a)))
         (else (mzero)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a) 
       (inc 
         (mplus* (bind* (g0 a) g ...) (bind* (g1 a) g^ ...) ...))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 (lambdaf@ () (mplus* e ...))))))

;; (define mplus
;;   (lambda (a-inf f)
;;     (case-inf a-inf
;;       (() (f))
;;       ((f^) (inc (mplus (f) f^)))
;;       ((a) (choice a f))
;;       ((a f^) (choice a (lambdaf@ () (mplus (f) f^)))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (a)
       (inc
         (let ((x (var 'x)) ...)
           (bind* (g0 a) g ...)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

;; redefined in tabling code
;; (define bind
;;   (lambda (a-inf g)
;;     (case-inf a-inf
;;       (() (mzero))
;;       ((f) (inc (bind (f) g)))
;;       ((a) (g a))
;;       ((a f) (mplus (g a) (lambdaf@ () (bind (f) g)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g ... 
            (lambdag@ (a)
              (cons (reify x a) '())))
          empty-s))))))

;; redefined in tabling code
;; (define take
;;   (lambda (n f)
;;     (if (and n (zero? n)) 
;;       '()
;;       (case-inf (f)
;;         (() '())
;;         ((f) (take n f))
;;         ((a) a)
;;         ((a f) (cons (car a) (take (and n (- n 1)) f)))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))
