#lang typed/racket
(require typed/rackunit)

; Full project implemented


; ***** Abstract Syntax *****

(define-type ExprC (U NumC BinopC Cond0C IdC AppC))

; EXPR
; num
(struct NumC([n : Real]) #:transparent)
; {op EXPR EXPR}
(struct BinopC([op : Symbol] [l : ExprC] [r : ExprC]) #:transparent)
; {ifleq0? EXPR : EXPR else: EXPR}
(struct Cond0C([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
; id
(struct IdC([s : Symbol]) #:transparent)
; {id {EXPR}}
(struct AppC([fun : IdC] [arg : ExprC]) #:transparent)

; DEFN
; {fun {id (id)} EXPR}
(struct FundefC([name : IdC] [arg : IdC] [body : ExprC]) #:transparent)


; ***** Parser *****

; given an Sexp, recursively map Sexp to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    ; parse real numbers
    [(? real? n) (NumC n)]
    ; parse function applications
    [(list name (list arg)) (AppC (parse-id name) (parse arg))]
    ; parse symbols to IdC
    [(? symbol? s) (parse-id s)]
    ; parse binary operations
    [(list (? symbol? s) l r) (BinopC (check-binop s) (parse l) (parse r))]
    ; parse ifleq0 statements
    [(list 'ifleq0? x ': y 'else: z) (Cond0C (parse x) (parse y) (parse z))]
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; given an Sexp, check Sexp against taken ids and parse symbol to IdC
(define (parse-id [s : Sexp]) : IdC
  (cond
    ; check against taken ids
    [(or (equal? s '+)
    (equal? s '-)
    (equal? s '*) 
    (equal? s '/)
    (equal? s 'fun)
    (equal? s 'ifleq0?) 
    (equal? s ':) 
    (equal? s 'else:)) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    ; legal id
    [(symbol? s) (IdC s)]
    ; catch illegal ids
    [else (error 'parse-id "PAIG: expected legal id, got ~e" s)]))

; given a symbol, check if it's a valid binary operator
(define (check-binop [s : Symbol]) : Symbol
  (cond
    [(equal? s '-) s]
    [(equal? s '+) s]
    [(equal? s '*) s]
    [(equal? s '/) s]
    [else (error 'check-binop "PAIG: expected legal binary operator, got ~e" s)]))

; given a PAIG function definition, create a corresponding FundefC
(define (parse-fundef [s : Sexp]) : FundefC
  (match s
    ; ensure main has 'init' as argument
    [(list 'fun (list 'main (list arg)) body) (cond
      [(equal? arg 'init) (FundefC (IdC 'main) (IdC 'init) (parse body))]
      [else (error 'parse-fundef "PAIG: expected \"init\" as argument to main, got ~e" arg)])]
    ; parse PAIG function definition
    [(list 'fun (list name (list arg)) body) (FundefC (parse-id name) (parse-id arg) (parse body))]
    ; catch illegal function definitions
    [other (error 'parse-fundef "PAIG: expected legal function definition, got ~e" other)]))

; given a list of PAIG functions (a PAIG program), parse into a list of FundefC
(define (parse-prog [s : Sexp]) : (Listof FundefC)
  (match s
    ['() '()]
    [(cons f r) (cons (parse-fundef f) (parse-prog r))]
    ; catch invalid program structure
    [other (error 'parse-prog "PAIG: expected legal program, got ~e" other)]))


; ***** Interpreter *****

; given an Sexp, combine parsing and evaluation to run program
(: top-interp (Sexp -> Real))
(define (top-interp fun-sexps)
  (interp-fns (parse-prog fun-sexps)))

; given the list of functions from a program, interprets the function named main from function definitions
(define (interp-fns [funs : (Listof FundefC)]) : Real
  ; evaluate program by applying main function to argument 0
  (interp (AppC (IdC 'main) (NumC 0)) funs))

; given an ExprC and list of FundefCs, recursively evaluate ExprCs to resolve applications
(define (interp [e : ExprC] [funs : (Listof FundefC)]) : Real
  (match e
    [(NumC n) n]
    ; use binop-lookup to assign meaning to binop
    [(BinopC s l r) (binop-lookup (BinopC s l r) funs)]
    ; check if x <= 0
    [(Cond0C x y z) (cond
      [(<= (interp x funs) 0) (interp y funs)]
      [else (interp z funs)])]
    ; find function, eagerly evaluate arguments, then evaluate body
    [(AppC f arg) (local ([define fd (find-fun f funs)]) 
                    (interp (subst (interp arg funs) (FundefC-arg fd) (FundefC-body fd)) funs))]))

; given the a function's argument, name, and body, substitute ExprC into given function body
(define (subst [arg : Real] [name : IdC] [body : ExprC]) : ExprC
  (match body
    [(NumC n) body]
    [(IdC s) (cond
               [(symbol=? s (IdC-s name)) (NumC arg)]
               [else (error 'subst "PAIG: \"~e\" is an unbound identifier" s)])]
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

; given a valid BinopC and a list of FundefCs, match BinopC's binary operator to its meaning and evaluate
(define (binop-lookup [b : BinopC] [funs : (Listof FundefC)]) : Real
  (match b
    [(BinopC '+ l r) (+ (interp l funs) (interp r funs))]
    [(BinopC '* l r) (* (interp l funs) (interp r funs)) ]
    [(BinopC '- l r) (- (interp l funs) (interp r funs)) ]
    [(BinopC '/ l r) (local ([define divisor (interp r funs)])
                       (cond
                         [(equal? 0 divisor) (error 'binop-lookup "PAIG: cannot divide by 0")]
                         [else (/ (interp l funs) divisor)]))]))


; ***** Test Cases *****

; round numbers to the nearest integer
(check-equal? (top-interp '{{fun {main (init)} {round (5.5)}}
  {fun {round (num)} {ifleq0? num : {+ 1 {* -1 {round-neg (num)}}} else: {- {round-pos (num)} 1}}}
  {fun {round-pos (num)} {ifleq0? num : 0 else: {+ 1 {round-pos ({- num 1})}}}}
  {fun {round-neg (num)} {ifleq0? num : {+  1 {round-neg ({+ num 1})}} else: 0}}}) 5)
(check-equal? (top-interp '{{fun {main (init)} {round (-5.5)}}
  {fun {round (num)} {ifleq0? num : {+ 1 {* -1 {round-neg (num)}}} else: {- {round-pos (num)} 1}}}
  {fun {round-pos (num)} {ifleq0? num : 0 else: {+ 1 {round-pos ({- num 1})}}}}
  {fun {round-neg (num)} {ifleq0? num : {+  1 {round-neg ({+ num 1})}} else: 0}}}) -5)

; general functionality
(check-equal? (interp-fns (parse-prog '{{fun {f (x)} {+ x 14}}
                             {fun {main (init)} {f (2)}}})) 16)
(check-equal? (interp-fns (parse-prog '{{fun {f (x)} {g ({/ x 2})}}
                             {fun {main (init)} {f (2)}}
                             {fun {g (x)} {* {/ 6 x} {- x 4}}}})) -18)
(check-equal? (top-interp '{{fun {f (x)} {ifleq0? x : x else: {- x 1}}}
                             {fun {main (init)} {f (-2)}}}) -2)
(check-equal? (top-interp '{{fun {f (x)} {ifleq0? x : x else: {- x 1}}}
                             {fun {main (init)} {f (2)}}}) 1)
(check-equal? (interp-fns (parse-prog '{{fun {main (init)} {* {f (5)} {g ({+ 1 2})}}}
                    {fun {f (x)} {ifleq0? x : 1 else: {f ({- x 1})}}}
                    {fun {g (z)} {* z {* z z}}}})) 27)
(check-equal? (top-interp '{{fun {f (x)} {- 5 x}}
                            {fun {g (x)} {* 2 {f ({+ 1 x})}}}
                            {fun {main (init)} {* {f ({* 3 -10})} {g (4)}}}}) 0)
(check-= (top-interp '{{fun {g (x)} {ifleq0? x : {/ x 2} else: {* x 2}}}
                            {fun {f (x)} {ifleq0? x : {g ({+ x 1})} else: {- x 1}}}
                            {fun {main (init)} {f (-2)}}}) -0.5 0.001)
(check-= (top-interp '{{fun {g (x)} {ifleq0? x : {/ x 2} else: {* x 2}}}
                            {fun {f (x)} {ifleq0? x : {g ({+ x 1})} else: {- x 1}}}
                            {fun {main (init)} {f (-1)}}}) 0 0.001)
(check-= (top-interp '{{fun {g (x)} {ifleq0? x : {/ x 2} else: {* x 2}}}
                            {fun {f (x)} {ifleq0? x : {g ({+ x 1})} else: {- x 1}}}
                            {fun {main (init)} {f (1)}}}) 0 0.001)
(check-= (top-interp '{{fun {g (x)} {ifleq0? x : {/ x 2} else: {* x 2}}}
                            {fun {f (x)} {ifleq0? x : {g ({+ x 1})} else: {g ({- x 1})}}}
                            {fun {main (init)} {f (2)}}}) 2 0.001)

; error checking functionality
(check-exn (regexp (regexp-quote "check-binop"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {a x 14}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "find-fun"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ x 14}}
                             {fun {main (init)} {g (2)}}}))))
(check-exn (regexp (regexp-quote "subst"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ x y}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse-prog"))
           (lambda () (interp-fns (parse-prog 3))))
(check-exn (regexp (regexp-quote "parse-fundef"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ x 14} {'wrong}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse-fundef"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ x 14}}
                             {fun {main (wrong)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)}
                               {ifgeq0? x : x else: {- x 1}}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (interp-fns (parse-prog '{{fun {* (x)} {+ x 14}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (interp-fns (parse-prog '{{fun {else: (x)} {+ x 14}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "binop-lookup"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {/ x 0}}
                                                {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "binop-lookup"))
           (lambda () (top-interp '((fun (ignoreit (x)) (+ 3 4))
                                    (fun (main (init)) (ignoreit ((/ 1 (+ 0 0)))))))))
(check-exn (regexp (regexp-quote "check-binop"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {a b c}}
                             {fun {main (init)} {f (2)}}}))))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (interp-fns (parse-prog '{{fun {f ((x))} {+ x 14}}
                             {fun {main (init)} {f(2)}}}))))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ (x) 14}}
                             {fun {main (init)} {f(2)}}}))))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ (x) 14}}
                             {fun {(main) (init)} {f(2)}}}))))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (interp-fns (parse-prog '{{fun {f (x)} {+ (x) 14}}
                             {(fun) {main (init)} {f(2)}}}))))