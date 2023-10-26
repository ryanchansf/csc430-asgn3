#lang typed/racket
(require typed/rackunit)

; Full project implemented


; new features
; - change abstract syntax
; - update parser and interpreter to handle new abstract syntax
; - add environments
; - serialize
; - booleans
; - closures (straight out of book)
; - desugar with to blam
; - user error raising
; - built-ins (equal, <=, *, -, etc)

; - why {Expr Expr ...} not {BlamC Expr ...}
; - why new env with r as mt-env instead of current env



; ***** Abstract Syntax *****

(define-type ExprC (U NumC IdC StrC CondC BlamC AppC))

; EXPR
; num
(struct NumC([n : Real]) #:transparent)

; id
(struct IdC([s : Symbol]) #:transparent)

; string
(struct StrC([s : String]) #:transparent)

; {Expr ? Expr else: Expr} conditionals
(struct CondC([if : ExprC] [then : ExprC] [else : ExprC]) #:transparent)

; {with {[Expr as id] ...} : Expr} local variables
; no abstract syntax, desugared into function application in parser

; {blam {id ...} Expr} anonymous functions
(struct BlamC([args : (Listof IdC)] [body : ExprC]) #:transparent)

; {Expr Expr ...} function applications
(struct AppC([f : ExprC] [args : (Listof ExprC)]) #:transparent)


; ENVIRONMENTS
(struct Binding([name : Symbol] [val : Value]) #:transparent)

(define-type Env (Listof Binding))
(define mt-env '())
(define extend-env cons)



(struct BoolV([val : Boolean]) #:transparent)
(struct NumV([val : Real]) #:transparent)
(struct StrV([val : String]) #:transparent)
(struct CloV([arg : Symbol] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV([val : (-> ExprC * ExprC)]) #:transparent)


(define-type Value (U NumV StrV BoolV CloV PrimV))

(define top-env (cons (Binding 'true (BoolV #t))
                      (cons (Binding 'false (BoolV #f))
                            (cons (Binding '+ (PrimV +))
                                  (cons (Binding '- (PrimV -))
                                        (cons (Binding '* (PrimV *))
                                              (cons (Binding '/ (PrimV /))
                                                    (cons (Binding '<= (PrimV <=))
                                                          (cons (Binding 'equal? (PrimV equal?)) '())))))))))


; ***** Parser *****

; given an Sexp, recursively map Sexp to ExprC
(define (parse [s : Sexp]) : ExprC
  (match s
    ; parse real numbers to NumC
    [(? real? n) (NumC n)]
    ; parse symbols to IdC
    [(? symbol? s) (parse-id s)]
    ; parse strings to StrC
    [(? string? s) (StrC s)]
    ; parse conditionals to CondC
    [(list c '? t 'else: e) (CondC (parse c) (parse t) (parse e))]
    ; parse functions to BlamC
    [(list 'blam (list (? symbol? args) ...) body) (BlamC (map parse args) (parse body))]
    ; desugar with to AppC and BlamC
    [(list 'with (list (? list? locals) ...) ': body) (AppC (BlamC (map desugar-id locals) (parse body)) (map desugar-expr locals))]
    ; parse function applications to AppC
    [(cons f (? list? r))] ;"TODO"
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; desugar with local expr to ExprC
(define (desugar-expr [locals : (Listof Sexp)] [body : Sexp]) : ExprC
  (match
    [(list expr 'as _) (parse expr)]
    [other (error 'desugar-expr "PAIG: expected valid with clause, got ~e" other)]))

; desugar with local id to IdC
(define (desugar-id [local : (Listof Sexp)] [body : Sexp]) : IdC
  (match
    [(list _ 'as id) (parse-id id)]
    [other (error 'desugar-id "PAIG: expected valid with clause, got ~e" other)]))

; given an Sexp, check Sexp against taken ids and parse symbol to IdC
(define (parse-id [s : Sexp]) : IdC
  (cond
    ; check against taken ids
    [(or (equal? s '?)
         (equal? s 'else:)
         (equal? s 'with) 
         (equal? s 'as)
         (equal? s 'blam)) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
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
    ; ensure main has no arguments
    [(list 'fun (list 'main args) body) (cond
                                          [(equal? args '()) (FundefC (IdC 'main) '() (parse body))]
                                          [else (error 'parse-fundef
                                                       "PAIG: expected no arguments to main, got ~e" args)])]
    ; parse PAIG function definition
    [(list 'fun (list name (list (? symbol? args) ...)) body)
     (cond
       [(equal? #f (check-duplicates (cast args (Listof Symbol))))
        (FundefC (parse-id name) (map parse-id (cast args (Listof Symbol))) (parse body))]
       [else (error 'parse-fundef "PAIG: no duplicate arguments, got ~e" args)])]
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
  (interp (AppC (IdC 'main) '()) funs))

; given an ExprC and list of FundefCs, recursively evaluate ExprCs to resolve applications
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(NumC n) n]
    ; any Id not substituted is unbound
    [(IdC s) (lookup s env)] 
    ; use binop-lookup to assign meaning to binop
    [(BinopC s l r) (binop-lookup (BinopC s l r) funs)]
    ; check if x <= 0
    [(Cond0C x y z) (cond
                      [(<= (interp x funs) 0) (interp y funs)]
                      [else (interp z funs)])]
    ; find function, eagerly evaluate arguments, then evaluate body
    [(AppC f vals) (cond
                     [(equal? (length vals) (length (BlamC-args f))) (interp f
                           (extend-env (map (λ (arg val) (Binding arg (interp val env))) (BlamC-args f) vals) mt-env))]
                     [else (error
                              'interp "PAIG: Incorrect number for arguments for function: \"~e\""
                              f)])]))

; lookup binding in environment
(define (lookup [s : IdC] [env : Env]) : Value
  (match env
    ['() (error 'lookup "PAIG: name not found: ~e" s)]
    [(cons (Binding name val) r) (cond
                                   [(symbol=? s name) val]
                                   [else (lookup s r)])]))


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


