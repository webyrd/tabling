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

(ftest "mutual recursion"
  (letrec
    ((f (tabled (x)
          (conde
            ((== x 0))
            ((g x)))))
     (g (tabled (x)
          (conde
            ((== x 1))
            ((f x))))))
    (run+ (q) (f q)))
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
