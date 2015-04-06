(define bridgeso
  (lambda (land1 land2 bridge)
    (conde
      [(== 'north land1)
       (== 'east land2)
       (== 1 bridge)]
      [(== 'middle land1)
       (== 'east land2)
       (== 2 bridge)]
      [(== 'south land1)
       (== 'east land2)
       (== 3 bridge)]
      [(== 'north land1)
       (== 'middle land2)
       (== 4 bridge)]
      [(== 'north land1)
       (== 'middle land2)
       (== 5 bridge)]
      [(== 'south land1)
       (== 'middle land2)
       (== 6 bridge)]
      [(== 'south land1)
       (== 'middle land2)
       (== 7 bridge)])))

(define single-connection
  (lambda (land1 land2 bridge)
    (conde
      [(bridgeso land1 land2 bridge)]
      [(bridgeso land2 land1 bridge)])))

(define connection
  (lambda (land1 land2 bridges)
    (conde
      [(== land1 land2) (== '() bridges)]
      [(fresh (land bridge bridges*)
         (== (cons (list land1 land bridge) bridges*) bridges)
         (single-connection land1 land bridge)
         (connection land land2 bridges*))])))

(run* (q)
  (fresh (land1 land2 bridge)
    (== (list land1 land2 bridge) q)
    (bridgeso land1 land2 bridge)))

(run* (q)
  (fresh (land1 land2 bridge)
    (== (list land1 land2 bridge) q)
    (single-connection land1 land2 bridge)))

(run 1 (bridges)
  (connection 'east 'middle bridges))

(run 6 (bridges)
  (connection 'east 'middle bridges))

(run 50 (bridges)
  (connection 'east 'middle bridges))

#|
((east north 1)
 (north east 1)
 (east middle 2)
 (middle north 4)
 (north middle 4))
|#


(define tabled-connection
  (tabled (land1 land2 bridges)
    (conde
      [(== land1 land2) (== '() bridges)]
      [(fresh (land bridge bridges*)
         (== (cons (list land1 land bridge) bridges*) bridges)
         (tabled-single-connection land1 land bridge)
         (tabled-connection land land2 bridges*))])))

(define tabled-bridgeso
  (tabled (land1 land2 bridge)
    (conde
      [(== 'north land1)
       (== 'east land2)
       (== 1 bridge)]
      [(== 'middle land1)
       (== 'east land2)
       (== 2 bridge)]
      [(== 'south land1)
       (== 'east land2)
       (== 3 bridge)]
      [(== 'north land1)
       (== 'middle land2)
       (== 4 bridge)]
      [(== 'north land1)
       (== 'middle land2)
       (== 5 bridge)]
      [(== 'south land1)
       (== 'middle land2)
       (== 6 bridge)]
      [(== 'south land1)
       (== 'middle land2)
       (== 7 bridge)])))

(define tabled-single-connection
  (tabled (land1 land2 bridge)
    (conde
      [(tabled-bridgeso land1 land2 bridge)]
      [(tabled-bridgeso land2 land1 bridge)])))
