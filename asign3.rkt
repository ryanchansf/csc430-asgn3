#lang typed/racket
(require typed/rackunit)

; Full project implemented

; Roadmap:
; - Lab 3 code
; - ifleq0?
; - Binop (+ - * /)
; - Functions and ids

; ***** Abstract Syntax *****
(struct NumC([n : Real]) #:transparent)
(struct BinopC([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
; ifleq0? x : y else: z
(struct Cond0C([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct IdC([s : Symbol]) #:transparent)
(struct AppC([fun : Symbol] [arg : ExprC]) #:transparent)
(define-type ExprC (U NumC BinopC Cond0C IdC AppC))

; functions
(struct FundefC([name : Symbol] [arg : Symbol] [body : ExprC]) #:transparent)


; ***** Parser *****
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

; given a PAIG function parse into a FundefC
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    ; destructure fundef, create a FunDefC, parse body
    ; should we check name against taken id's here or in parse-prog??
    [(list 'fun (list name (list arg)) body) (FundefC name arg (parse body))]
    ; better error check here?
    [other (error 'parse-fundef "PAIG: expected legal function definition, got ~e" other)]))

; given a list of PAIG functions, parse into a list of FundefC
(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    ['() '()]
    ; add more formatting here? enforce syntax?
    ; input is list of functions, so f is a function, r is a list of functions.
    ; use parse-fundef to parse a function, and then recursively call parse-prog
    ; to parse the rest of the functions
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]
    ; better error check here?
    [other (error 'parse-prog "PAIG: expected legal program, got ~e" other)]
    ))

; ***** Interpreter *****

; Combine parsing and evaluation to run program
(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

; interprets the function named main from function definitions
(define (interp-fns [funs : (Listof FundefC)]) : Real
  (match funs
    ; no main function
    ['() (error 'interp-fns "PAIG: couldn't find \"main\" function")]
    ; found main function
    [(cons (FundefC 'main arg body) r) (interp body funs)]
    ; check next function in list
    [(cons f r) (interp-fns r)]))

; recursively interpret ExprCs
(define (interp [e : ExprC] [funs : (Listof FundefC)]) : Real
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
; from asgn spec, should this return the function ex: (+)?
(define (binop-lookup [b : BinopC]) : Real
  (match b
    [(BinopC '+ l r) (+ (interp l) (interp r))]
    [(BinopC '* l r) (* (interp l) (interp r)) ]
    [(BinopC '- l r) (- (interp l) (interp r)) ]
    [(BinopC '/ l r) (/ (interp l) (interp r)) ]
    [other (error 'binop-lookup "PAIG: expected valid binop, got ~e" other)]))


; errors to check for
; - don't let other functions call main
; - check for taken ids
; - check for poorly created functions




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