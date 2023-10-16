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
(struct AppC([fun : IdC] [arg : ExprC]) #:transparent)
(define-type ExprC (U NumC BinopC Cond0C IdC AppC))

; functions
(struct FundefC([name : IdC] [arg : IdC] [body : ExprC]) #:transparent)


; ***** Parser *****
; recursively map Sexp to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (NumC n)]
    ; parse function applications
    [(list name (list arg)) (AppC (parse-id name) (parse arg))]
    ; parse symbols to IdC
    [(? symbol? s) (parse-id s)]
    ; parse binary operations
    [(list (? symbol? s) l r) (BinopC s (parse l) (parse r))]
    ; parse conditional statements
    [(list 'ifleq0? x ': y 'else: z) (Cond0C (parse x) (parse y) (parse z))]
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; check against taken ids and parse symbol
(define (parse-id [s : Sexp]) : IdC
  (cond
    [(equal? s '+) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s '-) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s '*) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s '/) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s 'fun) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s 'ifleq0?) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s ':) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    [(equal? s 'else:) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    ; come back to this
    [else (IdC (cast s Symbol))]))

; given a PAIG function parse into a FundefC
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    ; destructure fundef, create a FunDefC, parse body
    ; should we check name against taken id's here or in parse-prog??
    [(list 'fun (list 'main (list arg)) body) (cond
      [(equal? arg 'init) (FundefC (IdC 'main) (IdC 'init) (parse body))]
      [else (error 'parse-fundef "PAIG: expected \"init\" as argument to main, got ~e" arg)])]
    [(list 'fun (list name (list arg)) body) (FundefC (parse-id name) (parse-id arg) (parse body))]
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
  ; evaluate main function by finding main
  ;(interp (FundefC-body (find-fun (IdC 'main) funs)) funs))
  ; evaluate program by applying main function to argument 0
  (interp (AppC (IdC 'main) (NumC 0)) funs))


; recursively interpret ExprCs
(define (interp [e : ExprC] [funs : (Listof FundefC)]) : Real
  (match e
    [(NumC n) n]
    ; use binop-lookup to assign meaning to binop
    [(BinopC s l r) (binop-lookup (BinopC s l r) funs)]
    ; check if x <= 0
    ; add error checking here?
    [(Cond0C x y z) (cond
      [(<= (interp x funs) 0) (interp y funs)]
      [else (interp z funs)])]
    [(AppC f arg) (local ([define fd (find-fun f funs)]) 
                    (interp (subst (interp arg funs) (FundefC-arg fd) (FundefC-body fd)) funs))]))

; substitute ExprC into given function body
(define (subst [arg : Real] [name : IdC] [body : ExprC]) : ExprC
  (match body
    [(NumC n) body]
    [(IdC s) (cond
               [(symbol=? s (IdC-s name)) (NumC arg)]
               [else body])]
    [(AppC f a) (AppC f (subst arg name a))]
    [(BinopC s l r) (BinopC s (subst arg name l)
                            (subst arg name r))]
    [(Cond0C test then else) (Cond0C (subst arg name test) (subst arg name then) (subst arg name else))]))

; given function name, find corresponding FundefC
(define (find-fun [name : IdC] [funs : (Listof FundefC)]) : FundefC
  (match funs
    ['() (error 'find-fun "PAIG: expected defined function, got ~e" (IdC-s name))]
    [(cons (FundefC n arg body) r) (cond
      [(equal? n name) (FundefC name arg body)]
      [else (find-fun name r)])]))

; match binary operator to meaning
; from asgn spec, should this return the function ex: (+)?
(define (binop-lookup [b : BinopC] [funs : (Listof FundefC)]) : Real
  (match b
    [(BinopC '+ l r) (+ (interp l funs) (interp r funs))]
    [(BinopC '* l r) (* (interp l funs) (interp r funs)) ]
    [(BinopC '- l r) (- (interp l funs) (interp r funs)) ]
    [(BinopC '/ l r) (/ (interp l funs) (interp r funs)) ]
    [other (error 'binop-lookup "PAIG: expected valid binop, got ~e" other)]))


; errors to check for
; - don't let other functions call main?
; - check for taken ids
; - check for poorly created functions


(check-equal? (interp-fns (parse-prog '{{fun {f (x)} {+ x 14}}
                             {fun {main (init)} {f (2)}}}))16)
(check-equal? (interp-fns (parse-prog '{{fun {f (x)} {g ({/ x 2})}}
                             {fun {main (init)} {f (2)}}
                             {fun {g (x)} {* {/ 6 x} {- x 4}}}}))-18)
(check-equal? (top-interp '{{fun {f (x)} {ifleq0? x : x else: {- x 1}}}
                             {fun {main (init)} {f (-2)}}}) -2)
(check-equal? (top-interp '{{fun {f (x)} {ifleq0? x : x else: {- x 1}}}
                             {fun {main (init)} {f (2)}}}) 1) 

; interp test cases
;(check-equal? (interp (parse '{+ 1 2})) 3)
;(check-equal? (interp (parse '{- 1 2})) -1)
;(check-equal? (interp (parse '{* 1 2})) 2)
;(check-equal? (interp (parse '{/ 2 2})) 1)
;(check-equal? (interp (parse '{ifleq0? {+ 1 2} : 0 else: 1})) 1)
;(check-equal? (interp (parse '{ifleq0? {+ 1 2} : {* 1 3} else: {* {+ 1 2} {/ 6 2}}})) 9)
;(check-equal? (interp (parse '{ifleq0? {/ 6 {- 1 2}} : {- 1 5} else: {+ 1 1}})) -4)
; error test cases
#;(check-exn (regexp (regexp-quote "parse"))
           (lambda () (parse "illegal expr")))
#;(check-exn (regexp (regexp-quote "binop-lookup"))
           (lambda () (binop-lookup (BinopC '& (NumC 1) (NumC 2)))))