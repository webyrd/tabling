;; a -> b -> c -> a
;; d -> e -> f -> d

(define edge
  (lambda (in-node out-node)
    (conde
      [(== 'a in-node)
       (== 'b out-node)]
      [(== 'b in-node)
       (== 'c out-node)]
      [(== 'c in-node)
       (== 'a out-node)]
      [(== 'd in-node)
       (== 'e out-node)]
      [(== 'e in-node)
       (== 'f out-node)]
      [(== 'f in-node)
       (== 'd out-node)])))

(define path
  (lambda (in out p)
    (conde
      [(== in out) (== '() p)]
      [(fresh (node p^)
         (== (cons (list in node) p^) p)
         (edge in node)
         (path node out p^))])))

(define curried-path
  (lambda (in out)
    (lambda (p)
      (conde
        [(== in out) (== '() p)]
        [(fresh (node p^)
           (== (cons (list in node) p^) p)
           (edge in node)
           ((curried-path node out) p^))]))))

(define reachable
  (lambda (in out)
    (conde
      [(== in out)]
      [(fresh (node)
         (edge in node)
         (reachable node out))])))

; (run 1 (q) (reachable 'd 'a))




(run* (q)
  (fresh (in out)
    (== (list in out) q)
    (edge in out)))

(run 1 (p)
  (path 'a 'c p))

(run 3 (p)
  (path 'a 'c p))

(run 1 (p)
  ((curried-path 'a 'c) p))



(define tabled-path
  (tabled (in out p)
    (conde
      [(== in out) (== '() p)]
      [(fresh (node p^)
         (== (cons (list in node) p^) p)
         (edge in node)
         (tabled-path node out p^))])))

(define tabled-reachable
  (tabled (in out)
    (conde
      [(== in out)]
      [(fresh (node)
         (edge in node)
         (tabled-reachable node out))])))

(run 1 (q) (tabled-reachable 'd 'a))

#|
(define tabled-inside-out-path
  (lambda (p)
    (tabled (in out)
      (conde
        [(== in out) (== '() p)]
        [(fresh (node p^)
           (== (cons (list in node) p^) p)
           (edge in node)
           ((tabled-inside-out-path p^) node out))]))))

(run 10 (p)
  ((tabled-inside-out-path p) 'a 'c))
|#

(define smart-path
  (lambda (in out p)
    (conde
      [(== in out) (== '() p)
       (tabled-reachable in out)]
      [(fresh (node p^)
         (== (cons (list in node) p^) p)
         (tabled-reachable in node)
         (tabled-reachable node out)
         (edge in node)
         (smart-path node out p^))])))

#|
(define smart-path
  (lambda (in out p)
    (conde
      [(== in out) (== '() p)
       (tabled-reachable in out)]
      [(fresh (node p^)
         (== (cons (list in node) p^) p)
         (tabled-reachable in out)
         (edge in node)
         (smart-path node out p^))])))
|#

#!eof

(run 3 (p)
  (smart-path 'a 'c p))
