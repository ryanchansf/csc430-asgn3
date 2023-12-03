#lang typed/racket
(require typed/rackunit)

; Full project implemented


; ***** Abstract Syntax *****

(define-type ExprC (U NumC IdC StrC CondC BlamC AppC RecC Type))

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
(struct BlamC([args : (Listof IdC)] [types : (Listof Type)] [body : ExprC]) #:transparent)

; {Expr Expr ...} function applications
(struct AppC([f : ExprC] [args : (Listof ExprC)]) #:transparent)

; {rec [{blam {[id : ty] ...} expr} as id returning ty] : expr} recursion
(struct RecC([f : BlamC] [name : IdC] [ret : Type] [body : ExprC]) #:transparent)


; ***** Values *****
(define-type Value (U NumV StrV BoolV CloV PrimV))

(struct BoolV([val : Boolean]) #:transparent)
(struct NumV([val : Real]) #:transparent)
(struct StrV([val : String]) #:transparent)
(struct CloV([args : (Listof IdC)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV([val : (U (-> (Listof Value) Value) (-> (Listof Value) Nothing))]) #:transparent)


; ***** Environments *****

(define box-Value (inst box Value))
(struct Binding([name : Symbol] [val : (Boxof Value)]) #:transparent)
(define-type Env (Listof Binding))


; ***** Types ******
(struct TBinding([name : Symbol] [type : Type]) #:transparent)
(define-type TEnv (Listof TBinding))

(define-type Type (U NumT BoolT StrT FunT))

(struct NumT() #:transparent)
(struct BoolT() #:transparent)
(struct StrT() #:transparent)
(struct FunT ([args : (Listof Type)] [ret : Type]) #:transparent)

(define base-tenv (cons (TBinding 'true (BoolT))
                        (cons (TBinding 'false (BoolT))
                              (cons (TBinding '+ (FunT (list (NumT) (NumT)) (NumT)))
                                    (cons (TBinding '- (FunT (list (NumT) (NumT)) (NumT)))
                                          (cons (TBinding '* (FunT (list (NumT) (NumT)) (NumT)))
                                                (cons (TBinding '/ (FunT (list (NumT) (NumT)) (NumT)))
                                                      (cons (TBinding '<= (FunT (list (NumT) (NumT)) (BoolT)))
                                                            (cons (TBinding 'num-eq? (FunT (list (NumT) (NumT)) (BoolT)))
                                                                  (cons (TBinding 'str-eq? (FunT (list (StrT) (StrT)) (BoolT)))
                                                                        (cons (TBinding 'substring (FunT (list (StrT) (NumT) (NumT)) (StrT))) '())))))))))))


; ***** Interpreter *****

; given an Sexp, combine parse and evaluate, serialize final Value
(define (top-interp [s : Sexp]) : String
  (define expr (parse s))
  (type-check expr base-tenv)
  (serialize (interp expr top-env)))

; given an ExprC and list of FundefCs, recursively evaluate ExprCs to resolve applications
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    ; search env for binding
    [(IdC s) (unbox (lookup (IdC s) env))]
    ; evaluate conditional
    [(CondC c t e) (local ([define c-val (interp c env)])
                     (cond
                       [(equal? c-val (BoolV #t)) (interp t env)]
                       [(equal? c-val (BoolV #f)) (interp e env)]
                       [else (error 'interp "PAIG: expected boolean value from condition, got ~e" c-val)]))]
    ; evalute BlamC to CloV
    [(BlamC args types body) (CloV args body env)]
    ; interp function applications into CloV, extend env based on current
    [(AppC f vals) (local ([define f-value (interp f env)])
                     (cond
                       ; anonymous function application
                       [(CloV? f-value)
                        (cond
                          ; ensure correct number of arguments
                          [(equal? (length vals) (length (CloV-args f-value)))
                           (interp (CloV-body f-value)
                                   ; extend the env by combining arg-value bindings and closure env 
                                   (append
                                    (map (λ ([arg : IdC] [val : ExprC]) : Binding
                                           (Binding (IdC-s arg) (box-Value (interp val env)))) (CloV-args f-value) vals)
                                    ; since (interp f env) could add bindings, use closure's env not env
                                    (CloV-env f-value)))]
                          [else (error
                                 'interp "PAIG: Incorrect number of arguments for function: \"~e\""
                                 f-value)])]
                       ; built-in function application
                       [(PrimV? f-value) ((PrimV-val f-value) (map (λ ([val : ExprC]) : Value (interp val env)) vals))]
                       ; invalid function application
                       [else (error 'interp "PAIG: illegal function application, cannot apply ~e" f-value)]))]
    [(RecC f name type body) (local ([define new-env (append (list (Binding (IdC-s name) (box-Value (NumV 0)))) env)])
                             (define f-clo (CloV (BlamC-args f) (BlamC-body f) new-env))
                             (set-box! (lookup name new-env) f-clo)
                             (interp body new-env))]))


; ***** BUILT-IN FUNCTIONS *****

; given two values, add them together or error if illegal
(define (top-plus [vals : (Listof Value)]) : NumV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (+ (NumV-val l) (NumV-val r)))]
                                  [else (error '+ "PAIG: non-number operands to (+ a b) → real")]))]
    [else (error '+ "PAIG: Incorrect number of arguments to '+', expected 2, got ~e" (length vals))]))

; given two values, subtract them or error if illegal
(define (top-minus [vals : (Listof Value)]) : NumV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (- (NumV-val l) (NumV-val r)))]
                                  [else (error '- "PAIG: non-number operands to (- a b) → real")]))]
    [else (error '- "PAIG: Incorrect number of arguments to '-', expected 2, got ~e" (length vals))]))

; given two values, multiply them together or error if illegal
(define (top-mult [vals : (Listof Value)]) : NumV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (* (NumV-val l) (NumV-val r)))]
                                  [else (error '* "PAIG: non-number operands to (* a b) → real")]))]
    [else (error '* "PAIG: Incorrect number of arguments to '*', expected 2, got ~e" (length vals))]))

; given two values, divide them or error if illegal
(define (top-divide [vals : (Listof Value)]) : NumV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r))
                                   (cond
                                     [(equal? (NumV-val r) 0) (error '/ "PAIG: illegal divide by 0")]
                                     [else (NumV (/ (NumV-val l) (NumV-val r)))])]
                                  [else (error '/ "PAIG: non-number operands to (/ a b) → real")]))]
    [else (error '/ "PAIG: Incorrect number of arguments to '/', expected 2, got ~e" (length vals))]))

; given two values l and r, return l <= r or error if illegal
(define (top-<= [vals : (Listof Value)]) : BoolV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (BoolV (<= (NumV-val l) (NumV-val r)))]
                                  [else (error '<= "PAIG: non-number operands to (<= a b) → boolean")]))]
    [else (error '<= "PAIG: Incorrect number of arguments to '<=', expected 2, got ~e" (length vals))]))

; give two values l and r, return l == r and l is num and r is num, or error if illegal
(define (top-num-eq? [vals : (Listof Value)]) : BoolV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (BoolV (equal? (NumV-val l) (NumV-val r)))]
                                  [else (BoolV #f)]))]
    [else (error 'num-eq? "PAIG: Incorrect number of arguments to 'num-equal', expected 2, got ~e" (length vals))]))

; give two values l and r, return l == r and l is str and r is str, or error if illegal
(define (top-str-eq? [vals : (Listof Value)]) : BoolV
  (cond
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (StrV? l) (StrV? r)) (BoolV (equal? (StrV-val l) (StrV-val r)))]
                                  [else (BoolV #f)]))]
    [else (error 'str-eq? "PAIG: Incorrect number of arguments to 'str-equal', expected 2, got ~e" (length vals))]))


; given a string, start, and end position, return the corresponding substring
(define (top-substring [vals : (Listof Value)]) : StrV
  (cond
    ; make sure exactly three arguments were passed to substring
    [(equal? (length vals) 3)
     (local ([define str (first vals)] [define start (second vals)] [define end (third vals)])
       (cond
         ; check types of input values
         [(or
           (not (and (StrV? str) (NumV? start) (NumV? end)))
           (not (exact-integer? (NumV-val start)))
           (not (exact-integer? (NumV-val end))))
          (error 'substring "PAIG: 'substring' expects string and two integer indices")]
         ; check that end is greater than or equal to start
         [(< (NumV-val end) (NumV-val start)) (error 'substring "PAIG: End index cannot be less than start")]
         ; check that start and end are both less than or equal to the string length
         [(and
           (<= (NumV-val start) (string-length (StrV-val str)))
           (<= (NumV-val end) (string-length (StrV-val str)))
           ; return substring
           (StrV (substring (StrV-val str) (NumV-val start) (NumV-val end))))]
         [else (error 'substring "PAIG: String index out of bounds")]))]
    [else
     (error 'substring "PAIG: Incorrect number of arguments to 'substring', expected 3, got ~e" (length vals))]))


; top-env definition
(define top-env (cons (Binding 'true (box-Value (BoolV #t)))
                      (cons (Binding 'false (box-Value (BoolV #f)))
                            (cons (Binding '+ (box-Value (PrimV top-plus)))
                                  (cons (Binding '- (box-Value (PrimV top-minus)))
                                        (cons (Binding '* (box-Value (PrimV top-mult)))
                                              (cons (Binding '/ (box-Value (PrimV top-divide)))
                                                    (cons (Binding '<= (box-Value (PrimV top-<=)))
                                                                (cons (Binding 'num-eq? (box-Value (PrimV top-num-eq?)))
                                                                      (cons (Binding 'str-eq? (box-Value (PrimV top-str-eq?)))
                                                                            (cons (Binding 'substring (box-Value (PrimV top-substring))) '())))))))))))


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
    [(list 'blam (? list? args) body)
     (match args
       [(list (list id ': type) ...)
        (local ([define blam-args (map blam-arg (cast args (Listof (Listof Sexp))))])
          (cond
            [(equal? (check-duplicates blam-args) #f) (BlamC blam-args
                                                             (map blam-type (cast args (Listof (Listof Sexp))))
                                                             (parse body))]
            [else (error 'parse "PAIG: duplicate vars in ~e" blam-args)]))]
       [other (error 'parse "expected legal expression, got ~e" other)])]
    ; desugar with to AppC and BlamC
    [(list 'with (? list? locals) ... ': body)
     (local ([define with-vars (map with-id (cast locals (Listof (Listof Sexp))))])
       (cond
         [(equal? (check-duplicates with-vars) #f) (AppC (BlamC
                                                          with-vars
                                                          (map with-type (cast locals (Listof (Listof Sexp))))
                                                          (parse body))
                                                         (map with-expr (cast locals (Listof (Listof Sexp)))))]
         [else (error 'parse "PAIG: duplicate vars in ~e" with-vars)])
       )]
    ; parse recursion to RecC
    [(list 'rec (list f 'as name 'returning type) ': body) (local ([define fun (parse f)])
                                                             (cond
                                                               [(BlamC? fun) (RecC fun (parse-id name) (parse-type type) (parse body))]
                                                               [else (error 'parse "PAIG: recursive function must be a function")]))]
    ; parse function applications to AppC
    [(cons f (? list? r)) (AppC (parse f) (map parse r))]
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; desugar with local expr to ExprC
(define (with-expr [local : (Listof Sexp)]) : ExprC
  (match local
    [(list expr 'as _ ': _) (parse expr)]))
; invalid with clause always caught in desugar-id

; desugar with local id to IdC
(define (with-id [local : (Listof Sexp)]) : IdC
  (match local
    [(list _ 'as id ': _) (parse-id id)]
    [other (error 'with-id "PAIG: expected valid with clause, got ~e" other)]))

; desugar with local type to Type
(define (with-type [local : (Listof Sexp)]) : Type
  (match local
    [(list _ 'as _ ': type) (parse-type type)]))
; invalid with clause always caught in desugar-id

; parse blam arg to IdC
(define (blam-arg [param : (Listof Sexp)]) : IdC
  (match param
    [(list id ': _) (parse-id id)]
    [other (error 'blam-arg "PAIG: expected valid blam argument, got ~e" other)]))

; parse blam arg type to Type
(define (blam-type [param : (Listof Sexp)]) : Type
  (match param
    [(list _ ': type) (parse-type type)]
    [other (error 'blam-arg "PAIG: expected valid blam argument, got ~e" other)]))

; given an Sexp, check Sexp against taken ids and parse symbol to IdC
(define (parse-id [s : Sexp]) : IdC
  (cond
    ; check against taken ids
    [(or (equal? s '?)
         (equal? s 'else:)
         (equal? s 'with) 
         (equal? s 'as)
         (equal? s 'blam)
         (equal? s ':)
         (equal? s 'rec)
         (equal? s '->)
         (equal? s 'returning)) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    ; legal id
    [(symbol? s) (IdC s)]
    ; catch illegal ids
    [else (error 'parse-id "PAIG: expected legal id, got ~e" s)]))


; ***** Type Checker *****

; given an Sexp, parse a type
(define (parse-type [s : Sexp]) : Type
  (match s
    ; parse real numbers to type NumT
    ['num (NumT)]
    ; parse strings to StrT
    ['str (StrT)]
    ; parse booleans?
    ['bool (BoolT)]
    ; parse functions
    [(list args ... '-> ret) 
     (FunT (map parse-type (cast args (Listof Sexp))) (parse-type ret))]
    [other (error 'parse-type "PAIG: expected valid type, got ~e" other)]))

; given an ExprC and environment, type-check the expression
(define (type-check [e : ExprC] [env : TEnv]) : Type
  (match e
    ; type-check num
    [(NumC n) (NumT)]
    ; type-check string
    [(StrC s) (StrT)]
    ; type-check ids
    [(IdC s) (t-lookup (IdC s) env)]
    ; type-check if-expressions
    [(CondC if then else) (cond
                            [(equal? (BoolT) (type-check if env)) (local ([define then-type (type-check then env)])
                                                                    (cond
                                                                      [(equal? then-type (type-check else env)) then-type]
                                                                      [else (error 'type-check "PAIG: then and else expressions should have same type")]))]
                            [else (error 'type-check "PAIG: expected boolean condition to if")])]
    ; type-check applications
    [(AppC fun args) (local ([define f (type-check fun env)])
                     (cond
                       [(FunT? f) (cond
                                            [(equal? (length (FunT-args f)) (length args)) (cond
                                                                                             [(equal? #t (foldl (lambda ([t1 : Type] [t2 : Type] [res : Boolean])
                                                                                                                 (and res (equal? t1 t2))) #t (FunT-args f) (map (λ ([arg : ExprC]) : Type (type-check arg env)) args))) (FunT-ret f)]
                                                                                             [else (error 'type-check "PAIG: type mismatch between function parameters and arguments")])]
                                            [else (error 'type-check "PAIG: Incorrect number of arguments to function ~e" f)])]
                       [else (error 'type-check "PAIG: Cannot apply a non-function")]))]
    
    ; type-check BlamC terms
    [(BlamC args types body) (FunT types (type-check body
                                                    ; extend the type env by combining arg-type bindings and current env 
                                                    (append
                                                     (map (λ ([arg : IdC] [type : Type]) : TBinding
                                                            (TBinding (IdC-s arg) type)) args types)
                                                     env)))]
    ; type-check rec terms
    [(RecC f name type body) (local ([define new-env (append (list (TBinding (IdC-s name) (FunT (BlamC-types f) type))) env)])
                               (type-check f new-env)
                               (type-check body new-env))])) 


; lookup binding in type environment
(define (t-lookup [s : IdC] [env : TEnv]) : Type
  (match env
    ; binding doesn't exist
    ['() (error 't-lookup "PAIG: name not found: ~e" (IdC-s s))]
    [(cons (TBinding name type) r) (cond
                                     [(symbol=? (IdC-s s) name) type]
                                     [else (t-lookup s r)])]))
    

; ***** Misc Functions *****

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


; lookup binding in environment
(define (lookup [s : IdC] [env : Env]) : (Boxof Value)
  (match env
    ; binding doesn't exist
    ['() (error 'lookup "PAIG: name not found: ~e" (IdC-s s))]
    [(cons (Binding name box) r) (cond
                                   [(symbol=? (IdC-s s) name) box]
                                   [else (lookup s r)])]))



; ***** Test Cases *****

(check-equal? (top-interp '{rec [{blam {[n : num]} {{<= n 0} ? 0 else: {+ n {square-helper {- n 2}}}}}
                                 as square-helper returning num]
                             :
                             {with [{blam {[n : num]} {square-helper {- {* 2 n} 1}}}
                                    as square : {num -> num}]
                                   :
                                   {square 12}}}) "144")

; built-in functions

(check-equal? (top-interp '{* 1 2}) "2")
(check-equal? (top-interp '{/ 6 2}) "3")
(check-equal? (top-interp '{- 1 2}) "-1")
(check-equal? (top-interp '{<= 1 2}) "true")
(check-equal? (top-interp '{<= 3 2}) "false")
(check-equal? (top-interp '{num-eq? 1 1}) "true")
(check-equal? (top-interp '{num-eq? 2 1}) "false")
(check-equal? (top-interp '{str-eq? "a" "a"}) "true")
(check-equal? (top-interp '{str-eq? "b" "a"}) "false")

; general
(check-equal? (top-interp '{{blam ([x : num]) {+ x 1}} 2}) "3")
(check-equal? (top-interp '{{blam ([x : num] [y : num]) {+ x y}} 2 4}) "6")
(check-equal? (top-interp '{with [{blam ([x : num]) {+ x 1}} as f : {num -> num}] : {f 2}}) "3")
(check-equal? (top-interp '{with [{blam ([x : num]) {+ x 1}} as f : {num -> num}] : {f 2}}) "3")
(check-equal? (top-interp '{with [{blam ([x : num]) {+ x 1}} as f : {num -> num}] [{blam ([y : str]) 3} as g : {str -> num}] : {f {g "string"}}}) "4")
(check-equal? (top-interp '{with [{blam ([x : str]) {str-eq? x "5"}} as f : {str -> bool}] : {{f "5"} ? 5 else: 6}}) "5")
(check-equal? (top-interp '{with [{blam ([x : str]) {str-eq? x "5"}} as f : {str -> bool}] : {{f "4"} ? 5 else: 6}}) "6")
(check-equal? (top-interp '{blam ([x : num]) {+ x 1}}) "#<procedure>")
(check-equal? (top-interp '{{<= 1 2} ? "yes" else: "no"}) "\"yes\"")
(check-equal? (top-interp '{{blam ([x : {num num -> num}]) {x 3 4}} +}) "7")
(check-equal? (top-interp '{{blam ([x : {num num -> num}]) x} +}) "#<primop>")
(check-equal? (top-interp '{{blam () {num-eq? 2 2}}}) "true")
(check-equal? (top-interp '{{blam ([x : num]) 3} 3}) "3")
(check-equal? (top-interp '{{blam ([three : num]) three} {{blam ([x : num]) x} 3}}) "3")
(check-equal? (top-interp '{{blam ([three : {-> num}]) {three}} {{blam ([x : {num num -> num}]) {blam () {x 1 2}}} {blam ([x : num] [y : num]) {+ x y}}}}) "3")

; errors
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp '{error "checking user calling an error"})))
(check-exn (regexp (regexp-quote "error"))
           (lambda () (top-interp '{error})))
(check-exn (regexp (regexp-quote "+"))
           (lambda () (top-interp '{+ 3})))
(check-exn (regexp (regexp-quote "+"))
           (lambda () (top-interp '{+ 5 "hello"})))
(check-exn (regexp (regexp-quote "-"))
           (lambda () (top-interp '{- 3})))
(check-exn (regexp (regexp-quote "-"))
           (lambda () (top-interp '{- 5 "hello"})))
(check-exn (regexp (regexp-quote "*"))
           (lambda () (top-interp '{* 3 5 2})))
(check-exn (regexp (regexp-quote "*"))
           (lambda () (top-interp '{* 3 "hello"})))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 5 2})))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 0})))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 "hello"})))
(check-exn (regexp (regexp-quote "<="))
           (lambda () (top-interp '{<= 3 "hello"})))
(check-exn (regexp (regexp-quote "<="))
           (lambda () (top-interp '{<= 3 5 2})))
(check-exn (regexp (regexp-quote "equal?"))
           (lambda () (top-interp '{equal? 3 3 3})))
(check-exn (regexp (regexp-quote "with-id"))
           (lambda () (top-interp '{with [{blam (x) {+ x 1}} as f f] : {f 2}})))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (top-interp '{with [{blam (?) {+ x 1}} as f] : {f 2}})))
(check-exn (regexp (regexp-quote "lookup"))
           (lambda () (top-interp '{equal? f 3 3})))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{{blam (x) {+ x 1}} 3 4})))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{3 4})))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{3 ? 4 else: 5})))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (top-interp '{#f})))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (top-interp '{{blam ({x}) {+ x 1}} 3})))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (top-interp '{blam (x x) 3})))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (parse '{with [(blam () 3) as z] [9 as z] : (z)})))

