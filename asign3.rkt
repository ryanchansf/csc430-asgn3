#lang typed/racket
(require typed/rackunit)

; Full project implemented

; Roadmap:
; - Lab 3 code
; - ifleq0?
; - Binop (+ - * /)
; - Functions

; data definitions
(struct NumC([n : Real]) #:transparent)
(struct BinopC([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
(struct Cond0C([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(define-type ExprC (U NumC BinopC Cond0C))


; recursively map Sexp to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    ; only check if it's a symbol, catch invalid binop in binop-lookup
    ; add error check to enforce valid binops here?
    [(list (? symbol? s) l r) (BinopC s (parse l) (parse r))]
    ; parse conditional statements
    [(list 'ifleq0? x ': y 'else: z) (Cond0C (parse x) (parse y) (parse z))]
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; recursively interpret ExprCs
(define (interp [e : ExprC]) : Real
  (match e
    [(NumC n) n]
    ; use binop-lookup to assign meaning to binop
    [(BinopC s l r) (binop-lookup (BinopC s l r))]
    ; check if x <= 0
    ; add error checking here?
    [(Cond0C x y z) (cond
      [(<= (interp x) 0) (interp y)]
      [else (interp z)])]))

; match binary operator to meaning
(define (binop-lookup [b : BinopC]) : Real
  (match b
    [(BinopC '+ l r) (+ (interp l) (interp r))]
    [(BinopC '* l r) (* (interp l) (interp r)) ]
    [(BinopC '- l r) (- (interp l) (interp r)) ]
    [(BinopC '/ l r) (/ (interp l) (interp r)) ]
    [other (error 'binop-lookup "PAIG: expected valid binop, got ~e" other)]))






; interp test cases
(check-equal? (interp (parse '{+ 1 2})) 3)
(check-equal? (interp (parse '{- 1 2})) -1)
(check-equal? (interp (parse '{* 1 2})) 2)
(check-equal? (interp (parse '{/ 2 2})) 1)
(check-equal? (interp (parse '{ifleq0? {+ 1 2} : 0 else: 1})) 1)
(check-equal? (interp (parse '{ifleq0? {+ 1 2} : {* 1 3} else: {* {+ 1 2} {/ 6 2}}})) 9)
(check-equal? (interp (parse '{ifleq0? {/ 6 {- 1 2}} : {- 1 5} else: {+ 1 1}})) -4)
; error test cases
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (parse "illegal expr")))
(check-exn (regexp (regexp-quote "binop-lookup"))
           (lambda () (binop-lookup (BinopC '& (NumC 1) (NumC 2)))))