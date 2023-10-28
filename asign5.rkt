#lang typed/racket
(require typed/rackunit)

; Full project implemented


; new features
; @- change abstract syntax
; - update parser and interpreter to handle new abstract syntax
; @- add environments
; @- serialize
; @- booleans
; @- closures (straight out of book)
; @- desugar with to blam
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
(struct CloV([args : (Listof IdC)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV([val : (-> Value Value Value)]) #:transparent)

(define-type Value (U NumV StrV BoolV CloV PrimV))


(define top-env (cons (Binding 'true (BoolV #t))
                      (cons (Binding 'false (BoolV #f))
                            (cons (Binding '+ (PrimV top-plus))
                                  (cons (Binding '- (PrimV top-minus))
                                        (cons (Binding '* (PrimV top-mult))
                                              (cons (Binding '/ (PrimV top-divide))
                                                    (cons (Binding '<= (PrimV top-<=))
                                                          (cons (Binding 'equal? (PrimV top-equal?)) '())))))))))
; given two values, add them together or error if illegal
(define (top-plus [l : Value] [r : Value]) : NumV
  (cond
    [(and (NumV? l) (NumV? r)) (NumV (+ (NumV-val l) (NumV-val r)))]
    [else (error '+ "PAIG: non-number operands to (+ a b) → real")]))

; given two values, subtract them or error if illegal
(define (top-minus [l : Value] [r : Value]) : NumV
  (cond
    [(and (NumV? l) (NumV? r)) (NumV (- (NumV-val l) (NumV-val r)))]
    [else (error '- "PAIG: non-number operands to (- a b) → real")]))

; given two values, multiply them together or error if illegal
(define (top-mult [l : Value] [r : Value]) : NumV
  (cond
    [(and (NumV? l) (NumV? r)) (NumV (* (NumV-val l) (NumV-val r)))]
    [else (error '* "PAIG: non-number operands to (* a b) → real")]))

; given two values, divide them or error if illegal
(define (top-divide [l : Value] [r : Value]) : NumV
  (cond
    [(and (NumV? l) (NumV? r)) (cond
                                 [(equal? (NumV-val r) 0) (error '/ "PAIG: illegal divide by 0")]
                                 [else (NumV (/ (NumV-val l) (NumV-val r)))])]
    [else (error '/ "PAIG: non-number operands to (/ a b) → real")]))

; given two values l and r, return l <= r or error if illegal
(define (top-<= [l : Value] [r : Value]) : BoolV
  (cond
    [(and (NumV? l) (NumV? r)) (BoolV (<= (NumV-val l) (NumV-val r)))]
    [else (error '<= "PAIG: non-number operands to (<= a b) → boolean")]))

; give two values l and r, return l == r or error if illegal
(define (top-equal? [l : Value] [r : Value]) : BoolV
  (cond
    [(and (NumV? l) (NumV? r)) (BoolV (equal? (NumV-val l) (NumV-val r)))]
    [(and (StrV? l) (StrV? r)) (BoolV (equal? (StrV-val l) (StrV-val r)))]
    [(and (BoolV? l) (BoolV? r)) (BoolV (equal? (BoolV-val l) (BoolV-val r)))]
    [else (BoolV #f)]))

; ***** Serializer *****

; given a PAIG5 Value, return a string
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(StrV s) (format "~v" s)]
    [(BoolV b) (cond
                 [(equal? b #t) "true"]
                 [else "false"])]
    [(CloV a b e) "#<procedure>"]
    [(PrimV p) "#<primop>"]))


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
    [(cons f (? list? r)) (AppC (parse f) (map parse r))]
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; desugar with local expr to ExprC
(define (desugar-expr [local : (Listof Sexp)]) : ExprC
  (match local
    [(list expr 'as _) (parse expr)]
    [other (error 'desugar-expr "PAIG: expected valid with clause, got ~e" other)]))

; desugar with local id to IdC
(define (desugar-id [local : (Listof Sexp)]) : IdC
  (match local
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


; ***** Interpreter *****

; given an Sexp, combine parse and evaluate, serialize final Value
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; given an ExprC and list of FundefCs, recursively evaluate ExprCs to resolve applications
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    ; any Id not substituted is unbound
    [(IdC s) (lookup (IdC s) env)]
    ; evaluate conditional
    [(CondC c t e) (local ([define c-val (interp c env)])
                     (cond
                       [(equal? c-val (BoolV #t)) (interp t env)]
                       [(equal? c-val (BoolV #f)) (interp e env)]
                       [else (error 'interp "PAIG: expected boolean value from condition, got ~e" c-val)]))]
    ; evalute BlamC
    [(BlamC args body) (CloV args body env)]
    ; find function, eagerly evaluate arguments, then evaluate body
    ; interp f into CloV, extend env based on current
    [(AppC f vals) (local ([define f-value (interp f env)])
                     (cond
                       ; anonymous function application
                       [(CloV? f-value) (cond
                                          [(equal? (length vals) (length (CloV-args f-value)))
                                           (interp (CloV-body f-value)
                                                   (extend-env (map (λ ([arg : Symbol] [val : ExprC]) : Binding (Binding arg (interp val env))) (CloV-args f-value) vals) env))]
                                          [else (error
                                                 'interp "PAIG: Incorrect number of arguments for function: \"~e\""
                                                 f-value)])]
                       ; built-in function application
                       [(PrimV? f-value) (cond
                                           [(equal? (length vals) 2) ((PrimV-val f-value) (interp (first vals) env) (interp (second vals) env))]
                                           [else (error 'interp "PAIG: Incorrect number of arguments, expected 2, got ~e" (length vals))])]
                       [else (error 'interp "PAIG: illegal function application, cannot apply ~e" f-value)]))]))


; lookup binding in environment
(define (lookup [s : IdC] [env : Env]) : Value
  (match env
    ['() (error 'lookup "PAIG: name not found: ~e" s)]
    [(cons (Binding name val) r) (cond
                                   [(symbol=? (IdC-s s) name) val]
                                   [else (lookup s r)])]))




