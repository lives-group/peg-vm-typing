#lang racket
(require rackcheck
         peg-gen
         peg-gen/peg-gen-syntax)

(setSynFactory PEGStructF)

(define batchsz 500)

(define (lit->char x)
   (integer->char (+ 97 x))
)

(define (coalesce x y)
   (cond
     [(and (string? x) (integer? y))  (string-append x (string (lit->char y)))]
     [(and (integer? x) (integer? y)) (string-append (string (lit->char x)) (string (lit->char y)))]
     [(and (integer? x) (string? y))  (string-append (string (lit->char x)) y)]
     [(and (string? x) (string? y))  (string-append x y)]
     )
  )

(define (simplify-peg e ) 
    (match e
        [(struct GEps ())    (GKle (GLit #\a))]
        [(struct GLit (c))   (GLit (lit->char c))]
        [(struct GVar (s))    (GVar s)]
        [(struct GAlt (l r))  (GAlt (simplify-peg l) (simplify-peg r))]
        [(struct GSeq ((struct GEps ()) r)) (simplify-peg r) ]
        [(struct GSeq (l (struct GEps ()))) (simplify-peg l)]
      
        [(struct GSeq ((struct GLit (l1)) (struct GSeq ((struct GLit (l2)) r)))) (simplify-peg (GSeq ((GLit (coalesce l1 l2)) r)))]
        [(struct GSeq ((struct GLit (l1))  (struct GLit (l2)))) (GLit (coalesce l1 l2))]
        ;[(struct GSeq (l (struct GEps ()))) (simplify-peg l)]

        [(struct GSeq (l r)) (GSeq (simplify-peg l) (simplify-peg r) )]
        [(struct GKle (p))   (GKle (simplify-peg p))  ]
        [(struct GNot (p))   (GNot (simplify-peg p)) ]
     )
  )

(define (simplify-gpeg g)
    (GPEG (make-immutable-hash (hash-map (GPEG-nt g)
                              (lambda (s exp) (cons s (simplify-peg exp)) )))
          (simplify-peg (GPEG-start g))
          (GPEG-gamma g))
  )

(define (expr-prec->string n e ) 
    (match e
        [(struct GEps ())    "ϵ"]
        [(struct GLit (c))    (cond
                                [(char? c) (string-append "\"" (string c) "\"")]
                                [(string? c) (string-append "\"" c "\"")]
                                [else (string-append "\"" (~a c) "\"")]) ]
        [(struct GVar (s))    (cond
                                [(string? s) s]
                                [else (~a s)]
                                )]
        [(struct GAlt (l r)) (parens (> n 2) (string-append (expr-prec->string 2 l) "/"
                                                           (expr-prec->string 2 r)))]
        [(struct GSeq (l r)) (parens (> n 1) (string-append (expr-prec->string 1 l)
                                                           (expr-prec->string 1 r)))]
        [(struct GKle (p))   (parens (> n 4) (string-append (expr-prec->string 4 p) "*"))  ]
        [(struct GNot (p))   (parens (> n 3) (string-append "!" (expr-prec->string 3 p) )) ]
     )
  )

(define (gpeg->string e )
    (foldr string-append
            ""
            (append (hash-map (GPEG-nt e)
                              (lambda (s exp) (string-append (~a s) " --> " (expr-prec->string 0 exp) ";\n")) )
                    (list "@start: " (expr-prec->string 0 (GPEG-start e)))
             )
    )
)


(define (parens b  s) 
     (match b
           [#f   s]
           [else  (string-append "(" s ")")]
  )
)

(define (mk-peg-strlist qtd)
   (let* ([xs (sample (gen:peg 3 3 3) qtd)])
      (map (lambda (x)  (gpeg->string (simplify-gpeg x))) xs)
   )
 )

(define (write-pegs paths pegs)
    (cond
      [(null? paths) (displayln 'batch-done)]
      [else (let ([out (open-output-file (car paths) #:mode 'text #:exists 'replace)])
              (begin
                (display (car pegs) out)
                (close-output-port out)
                (write-pegs (cdr paths) (cdr pegs)) ))])
  )

(define (mk-names p prf fc [sz 0])
     (cond
       [(< sz batchsz) (cons (string-append p  prf "_" (~v (+ fc sz)) ".txt" )
                             (mk-names p prf fc (+ sz 1)))]
       [else '()])    
  )

(define (mk-peg-batch path prefx-name qtd [fcounter 0])
  (cond
    [(<= qtd 0)  void]
    [(> qtd batchsz) (write-pegs (mk-names path prefx-name fcounter) (mk-peg-strlist batchsz))
                     (mk-peg-batch path prefx-name (- qtd batchsz) (+ fcounter batchsz))]
    [else (write-pegs (mk-names path prefx-name fcounter) (mk-peg-strlist qtd))])
 )