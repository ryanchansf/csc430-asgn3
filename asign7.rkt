#lang typed/racket
(require typed/rackunit)

; full project implemented


; ***** Abstract Syntax *****

(define-type ExprC (U NumC IdC StrC CondC BlamC AppC MutC))

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

; {id := expr} mutation
(struct MutC([id : IdC] [new : ExprC]) #:transparent)


; ***** Values *****
(define-type Value (U NumV StrV BoolV CloV PrimV ArrV NullV))

(struct BoolV([val : Boolean]) #:transparent)
(struct NumV([val : Real]) #:transparent)
(struct StrV([val : String]) #:transparent)
(struct CloV([args : (Listof IdC)] [body : ExprC] [env : Env]) #:transparent)
(struct PrimV([val : (-> (Listof Value) (Mutable-Vectorof Value) Value)]) #:transparent)
(struct ArrV([head : Natural] [tail : Natural]) #:transparent)
(struct NullV())



; ***** Environments *****

(struct Binding([name : Symbol] [loc : Natural]) #:transparent)
(define-type Env (Listof Binding))


; ***** Interpreter *****

; given an Sexp, combine parse and evaluate, serialize final Value
(define (top-interp [s : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse s) top-env (make-initial-store memsize))))


; given an ExprC, a list of FundefCs, and a store, recursively evaluate ExprCs to resolve applications
(define (interp [e : ExprC] [env : Env] [store : (Mutable-Vectorof Value)]) : Value
  (match e
    [(NumC n) (NumV n)]
    [(StrC s) (StrV s)]
    ; search env for binding, if found, get from store
    [(IdC s) (vector-ref store (lookup (IdC s) env))]
    ; evaluate conditional
    [(CondC c t e) (local ([define c-val (interp c env store)])
                     (cond
                       [(equal? c-val (BoolV #t)) (interp t env store)]
                       [(equal? c-val (BoolV #f)) (interp e env store)]
                       [else (error 'interp "PAIG: expected boolean value from condition, got ~e" c-val)]))]
    ; evaulate mutation
    [(MutC id new) (vector-set! store (lookup id env) (interp new env store))
                   (NullV)]
    ; evalute BlamC to CloV
    [(BlamC args body) (CloV args body env)]
    ; interp function applications into CloV, extend env based on current
    [(AppC f vals) (local ([define f-value (interp f env store)])
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
                                           (Binding (IdC-s arg)
                                                    (allocate store (list (interp val env store)))))
                                         (CloV-args f-value) vals)
                                    ; since (interp f env store) could add bindings, use closure's env not env
                                    (CloV-env f-value)) store)]
                          [else (error
                                 'interp "PAIG: Incorrect number of arguments for function: \"~e\""
                                 f-value)])]
                       ; built-in function application
                       [(PrimV? f-value) ((PrimV-val f-value)
                                          (map (λ ([val : ExprC]) : Value (interp val env store)) vals) store)]
                       ; invalid function application
                       [else (error 'interp "PAIG: illegal function application, cannot apply ~e" f-value)]))]))


; lookup binding in environment
(define (lookup [s : IdC] [env : Env]) : Natural
  (match env
    ; binding doesn't exist
    ['() (error 'lookup "PAIG: name not found: ~e" (IdC-s s))]
    [(cons (Binding name loc) r) (cond
                                   [(symbol=? (IdC-s s) name) loc]
                                   [else (lookup s r)])]))


; ***** Built-In Functions *****

; given a message, throw a user error
(define (top-error [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : Nothing
  (cond
    ; make sure exactly one argument was passed to error
    [(equal? (length vals) 1) (error 'user-error "PAIG: user-error: ~e" (serialize (first vals)))]
    [else (error 'error "PAIG: Incorrect number of arguments to error, expected 1, got ~e" (length vals))]))

; given two values, add them together or error if illegal
(define (top-plus [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : NumV
  (cond
    ; make sure exactly two arguments were passed to plus
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (+ (NumV-val l) (NumV-val r)))]
                                  [else (error '+ "PAIG: non-number operands to (+ a b) → real")]))]
    [else (error '+ "PAIG: Incorrect number of arguments to '+', expected 2, got ~e" (length vals))]))

; given two values, subtract them or error if illegal
(define (top-minus [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : NumV
  (cond
    ; make sure exactly two arguments were passed to minus
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (- (NumV-val l) (NumV-val r)))]
                                  [else (error '- "PAIG: non-number operands to (- a b) → real")]))]
    [else (error '- "PAIG: Incorrect number of arguments to '-', expected 2, got ~e" (length vals))]))

; given two values, multiply them together or error if illegal
(define (top-mult [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : NumV
  (cond
    ; make sure exactly two arguments were passed to mult
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (NumV (* (NumV-val l) (NumV-val r)))]
                                  [else (error '* "PAIG: non-number operands to (* a b) → real")]))]
    [else (error '* "PAIG: Incorrect number of arguments to '*', expected 2, got ~e" (length vals))]))

; given two values, divide them or error if illegal
(define (top-divide [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : NumV
  (cond
    ; make sure exactly two arguments were passed to divide
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r))
                                   (cond
                                     [(equal? (NumV-val r) 0) (error '/ "PAIG: illegal divide by 0")]
                                     [else (NumV (/ (NumV-val l) (NumV-val r)))])]
                                  [else (error '/ "PAIG: non-number operands to (/ a b) → real")]))]
    [else (error '/ "PAIG: Incorrect number of arguments to '/', expected 2, got ~e" (length vals))]))

; given two values l and r, return l <= r or error if illegal
(define (top-<= [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : BoolV
  (cond
    ; make sure exactly two arguments were passed to <=
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (BoolV (<= (NumV-val l) (NumV-val r)))]
                                  [else (error '<= "PAIG: non-number operands to (<= a b) → boolean")]))]
    [else (error '<= "PAIG: Incorrect number of arguments to '<=', expected 2, got ~e" (length vals))]))

; given two values l and r, return l == r or error if illegal
(define (top-equal? [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : BoolV
  (cond
    ; make sure exactly two arguments were passed to equal?
    [(equal? (length vals) 2) (local ([define l (first vals)] [define r (second vals)])
                                (cond
                                  [(and (NumV? l) (NumV? r)) (BoolV (equal? (NumV-val l) (NumV-val r)))]
                                  [(and (StrV? l) (StrV? r)) (BoolV (equal? (StrV-val l) (StrV-val r)))]
                                  [(and (BoolV? l) (BoolV? r)) (BoolV (equal? (BoolV-val l) (BoolV-val r)))]
                                  [(and (ArrV? l) (ArrV? r)) (BoolV (and (equal? (ArrV-head l) (ArrV-head r))
                                                                         (equal? (ArrV-tail l) (ArrV-tail r))))]
                                  [(and (NullV? l) (NullV? r)) (BoolV #t)]
                                  [else (BoolV #f)]))]
    [else (error 'equal? "PAIG: Incorrect number of arguments to 'equal', expected 2, got ~e" (length vals))]))

; given two values size and initial value, create an array
(define (top-make-array [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : ArrV
  (cond
    ; make sure exactly two arguments were passed to make-array
    [(equal? (length vals) 2) (local ([define n-value (first vals)] [define init (second vals)])
                                (cond
                                  ; make sure size is a number and an integer
                                  [(and (NumV? n-value) (exact-integer? (NumV-val n-value)))
                                   (define n (NumV-val n-value))
                                                   (cond
                                                     ; make sure size isn't 0, allocate array
                                                     [(> n 0)
                                                      (define head
                                                        (allocate store
                                                                  (build-list n (λ ([i : Integer]) : Value init))))
                                                      (ArrV head (+ head (- n 1)))]
                                                     [else
                                                      (error
                                                       'make-array "PAIG: Illegal to create an
array with fewer than one cell")])]
                                  [else (error 'make-array "PAIG: size of array must be an integer")]))]
    [else
     (error 'make-array "PAIG: Incorrect number of arguments to 'make-array', expected 2, got ~e" (length vals))]))

; given a list of values, create an array of those values
(define (top-array [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : ArrV
  (define n (length vals))
  (cond
    ; make sure there are items to place in array, allocate array
    [(> n 0) (define head (allocate store vals))
             (ArrV head (+ head (- n 1)))]
    [else (error 'array "PAIG: Illegal to create an array with fewer than one cell")]))

; given an array and an index, return the element at that index
(define (top-aref [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : Value
  (cond
    ; make sure exactly two arguments were passed to aref
    [(equal? (length vals) 2)
     (local ([define arr (first vals)] [define index-value (second vals)])
       (cond
         ; make sure arr and index-value have correct types
         [(and (ArrV? arr) (NumV? index-value)) (define index (NumV-val index-value))
                                                (cond
                                                  ; make sure index is an exact integer
                                                  [(exact-integer? index)
                                                   (local
                                                     ([define size (+ (- (ArrV-tail arr) (ArrV-head arr)) 1)])
                                                     (cond
                                                       ; make sure index is within array bounds
                                                       [(and (< index size) (>= index 0))
                                                        (vector-ref store (+ (ArrV-head arr) index))]
                                                       [else (error 'aref "PAIG: Array index out of bounds")]))]
                                                  [else (error 'aref "PAIG: cell index must be an exact integer")])]
         [else (error 'aref "PAIG: aref expects an array and integer as arguments")]))]
    [else (error 'aref "PAIG: Incorrect number of arguments to aref, expected 2, got ~e" (length vals))]))

; given an array, an index, and a value, set the element at the index to the value
(define (top-aset! [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : NullV
  (cond
    ; make sure exactly three arguments were passed to aset!
    [(equal? (length vals) 3)
     (local ([define arr (first vals)] [define index-value (second vals)] [define val (third vals)])
       (cond
         ; make sure arr and index-value have correct types
         [(and (ArrV? arr) (NumV? index-value))
          (define index (NumV-val index-value))
          (cond
            ; make sure index is an exact integer
            [(exact-integer? index)
             (local ([define size (+ (- (ArrV-tail arr) (ArrV-head arr)) 1)])
               (cond
                 ; make sure index is within array bounds
                 [(and (< index size) (>= index 0)) (vector-set! store (+ (ArrV-head arr) index) val)
                                                    (NullV)]
                 [else (error 'aset! "PAIG: Array index out of bounds")]))]
            [else (error 'aset! "PAIG: cell index must be an exact integer")])]
         [else (error 'aset! "PAIG: aset! expects an array and integer as first 2 arguments")]))]
    [else (error 'aset! "PAIG: Incorrect number of arguments to aref, expected 2, got ~e" (length vals))]))

; given a sequence of expressions, evaluate each and return the last one
(define (top-do [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : Value
  (last vals))

; given a string, start, and end position, return the corresponding substring
(define (top-substring [vals : (Listof Value)] [store : (Mutable-Vectorof Value)]) : StrV
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
(define top-env (cons (Binding 'true 1) (cons (Binding 'false 2) (cons (Binding '+ 3)
                    (cons (Binding '- 4) (cons (Binding '* 5) (cons (Binding '/ 6)
                      (cons (Binding '<= 7) (cons (Binding 'error 8) (cons (Binding 'equal? 9)
                            (cons (Binding 'make-array 10) (cons (Binding 'array 11)
                               (cons (Binding 'aref 12) (cons (Binding 'aset! 13)
                                  (cons (Binding 'do 14) (cons (Binding 'substring 15) '()))))))))))))))))


; ***** Store *****

; creates the initial store containing values for top-env names
(define (make-initial-store [n : Natural]) : (Mutable-Vectorof Value)
  (define make-value-vector (inst make-vector Value))
  (cond
    [(< n 16) (error 'make-initial-store "PAIG: Out of memory")]
    [else (define store (make-value-vector n (NumV 0)))
           ; set first element to index of first open element
           (vector-set! store (ann 0 Natural) (NumV 16))
           ; add top-env values
           (vector-set! store (ann 1 Natural) (BoolV #t))
           (vector-set! store (ann 2 Natural) (BoolV #f))
           (vector-set! store (ann 3 Natural) (PrimV top-plus))
           (vector-set! store (ann 4 Natural) (PrimV top-minus))
           (vector-set! store (ann 5 Natural) (PrimV top-mult))
           (vector-set! store (ann 6 Natural) (PrimV top-divide))
           (vector-set! store (ann 7 Natural) (PrimV top-<=))
           (vector-set! store (ann 8 Natural) (PrimV top-error))
           (vector-set! store (ann 9 Natural) (PrimV top-equal?))
           (vector-set! store (ann 10 Natural) (PrimV top-make-array))
           (vector-set! store (ann 11 Natural) (PrimV top-array))
           (vector-set! store (ann 12 Natural) (PrimV top-aref))
           (vector-set! store (ann 13 Natural) (PrimV top-aset!))
           (vector-set! store (ann 14 Natural) (PrimV top-do))
           (vector-set! store (ann 15 Natural) (PrimV top-substring))
           store]))

; add a list of values to the store at first available memory
(define (allocate [s : (Mutable-Vectorof Value)] [vals : (Listof Value)]) : Natural
  ; store[0] is always a NumV, user cannot change it, so casting always works
  ; (NumV-val store[0]) is always a natural, user cannot change it, so casting always works
  (define base (cast (NumV-val (cast (vector-ref s 0) NumV)) Natural))
  (cond
    [(> (+ (length vals) base) (vector-length s)) (error 'allocate "PAIG: Out of memory")]
    [else (for ([val vals]
                [i : Integer (in-range base (+ base (length vals)))])
            (vector-set! s i val))
          (vector-set! s (ann 0 Natural) (NumV (+ (length vals) base)))
          base]))


; ***** Serializer *****

; given a PAIG5 Value, return a string
(define (serialize [val : Value]) : String
  (match val
    [(NumV n) (format "~v" n)]
    [(StrV s) (format "~v" s)]
    [(BoolV b) (cond
                 [(equal? b #t) "true"]
                 [else "false"])]
    [(CloV _ _ _) "#<procedure>"]
    [(PrimV _) "#<primop>"]
    [(ArrV _ _) "#<array>"]
    [(NullV) "null"]))


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
    ; parse mutations to MutC
    [(list id ':= new) (MutC (parse-id id) (parse new))]
    ; parse functions to BlamC
    [(list 'blam (? list? args) body)
     (cond
       [(equal? #f (check-duplicates args)) (BlamC (map parse-id (cast args (Listof Sexp))) (parse body))]
       [else (error 'parse "PAIG: duplicate arguments: ~e" args)])]
    ; desugar with to AppC and BlamC
    [(list 'with (? list? locals) ... ': body)
     (local ([define with-vars (map desugar-id (cast locals (Listof (Listof Sexp))))])
       (cond
         [(equal?
           (check-duplicates with-vars) #f) (AppC (BlamC
                                                   with-vars
                                                   (parse body))
                                                  (map desugar-expr (cast locals (Listof (Listof Sexp)))))]
         [else (error 'parse "PAIG: duplicate vars in ~e" with-vars)])
       )]
    ; parse function applications to AppC
    [(cons f (? list? r)) (AppC (parse f) (map parse r))]
    ; catch illegal expressions
    [other (error 'parse "PAIG: expected legal expression, got ~e" other)]))

; desugar with local expr to ExprC
(define (desugar-expr [local : (Listof Sexp)]) : ExprC
  (match local
    [(list expr 'as _) (parse expr)]))
; invalid with clause always caught in desugar-id

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
         (equal? s ':=)
         (equal? s ':)
         (equal? s 'blam)) (error 'parse-id "PAIG: expected legal id, got ~e" s)]
    ; legal id
    [(symbol? s) (IdC s)]
    ; catch illegal ids
    [else (error 'parse-id "PAIG: expected legal id, got ~e" s)]))





; ***** Test Cases *****


; accepts a guard function and a body function and keeps running body until guard returns false
(define while : Sexp
  '{with ["bogus" as while] :
         {do {while := {blam {self guard body}
                      {{guard} ? {do {body} {self self guard body}}
                              else: {body := 200}}}}
           while}})

; given an array and its size, return true if the array is in strictly increasing order
(define in-order : Sexp
  '{with ["bogus" as in-order] :
         {do {in-order := {blam (arr size)
                                {with [0 as i][{<= 1 2} as res] :
                                      {do {while while
                                                 {blam () {<= i {- size 2}}}
                                                 {blam () {do
                                                              {{equal? {aref arr i} {aref arr {+ i 1}}}
                                                               ? {res := {<= 2 1}} else: "pass"}
                                                            {{<= {aref arr i} {aref arr {+ i 1}}}
                                                             ? "pass" else: {res := {<= 2 1}}}
                                                            {i := {+ i 1}}}}}
                                        res}}}}
           in-order}})


(top-interp (quasiquote {with [(unquote while) as while] :
                              {with [(unquote in-order) as in-order] :
                                    {+ {{in-order {array 5 6 7} 3} ? 1 else: 0}
                                       {{in-order {array 1 2 3 4} 4} ? 4 else: 2}}
                                    }}) 200)

(check-exn (regexp (regexp-quote "allocate"))
           (lambda () (top-interp '{with [{array 3 3 3 3 3 3 3 3} as arr] : {aset! arr 1 2}} 18)))
(check-exn (regexp (regexp-quote "make-initial-store"))
           (lambda () (top-interp '{with [{array 3 3 3 3 3 3 3 3} as arr] : {aset! arr 1 2}} 10)))
(check-exn (regexp (regexp-quote "substring"))
           (lambda () (top-interp '{substring 1 2 3} 25)))
(check-exn (regexp (regexp-quote "substring"))
           (lambda () (top-interp '{substring "hello" 3 2} 25)))
(check-exn (regexp (regexp-quote "substring"))
           (lambda () (top-interp '{substring "hello" 2 6} 25)))
(check-exn (regexp (regexp-quote "substring"))
           (lambda () (top-interp '{substring "hello" 2 6 1} 25)))
(check-exn (regexp (regexp-quote "aset!"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aset! arr 3 1}} 25)))
(check-exn (regexp (regexp-quote "aset!"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aset! arr 1.2 1}} 25)))
(check-exn (regexp (regexp-quote "aset!"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aset! arr "a" 1}} 25)))
(check-exn (regexp (regexp-quote "aset!"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aset! arr 3 1 1}} 25)))
(check-exn (regexp (regexp-quote "aref"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aref arr 3}} 25)))
(check-exn (regexp (regexp-quote "aref"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aref arr 1.2}} 25)))
(check-exn (regexp (regexp-quote "aref"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aref arr "a"}} 25)))
(check-exn (regexp (regexp-quote "aref"))
           (lambda () (top-interp '{with [{ array 1 2} as arr] : {aref arr 0 1}} 25)))
(check-exn (regexp (regexp-quote "array"))
           (lambda () (top-interp '{with [{array} as arr] : 3} 25)))
(check-exn (regexp (regexp-quote "make-array"))
           (lambda () (top-interp '{with [{make-array 0 1} as arr] : {aref arr 1}} 25)))
(check-exn (regexp (regexp-quote "make-array"))
           (lambda () (top-interp '{with [{make-array "3" 1} as arr] : {aref arr 1}} 25)))
(check-exn (regexp (regexp-quote "make-array"))
           (lambda () (top-interp '{with [{make-array 1.2 1} as arr] : {aref arr 1}} 25)))
(check-exn (regexp (regexp-quote "make-array"))
           (lambda () (top-interp '{with [{make-array 0 1 2} as arr] : {aref arr 1}} 25)))


; arrays
(check-equal? (top-interp '{{blam (x) {make-array 3 x}} 4} 100) "#<array>")
(check-equal? (top-interp '{do {{blam (x) {make-array 3 x}} 4} 5} 100) "5")
(check-equal? (top-interp '{aref {make-array 3 4} 1} 100) "4")
(check-equal? (top-interp '{with [{make-array 3 4} as arr] : {aref arr 2}} 100) "4")
(check-equal? (top-interp '{with [{array 1 2 3 4} as arr] : {aref arr 2}} 100) "3")
(check-equal? (top-interp '{with [{array 1 2 3 4} as arr] : {do {aset! arr 0 2} {aref arr 0}}} 100) "2")
(check-equal? (top-interp '{{blam (x) {do {x := 5} x}} 2} 100) "5")
(check-equal? (top-interp '{substring "hello" 0 2} 100) "\"he\"")
(check-equal? (top-interp '{with [{make-array 3 3} as arr] : {aset! arr 1 2}} 100) "null")
(check-equal? (top-interp '{with [{make-array 2 2} as arr] : {equal? arr arr}} 25) "true")
(check-equal? (top-interp '{with [{make-array 2 2} as arr] : {equal? arr 2}} 25) "false")
(check-equal? (top-interp '{with [{make-array 2 2} as arr] : {equal? {arr := 1} {arr := 2}}} 25) "true")
(check-equal? (top-interp '{with [{make-array 2 2} as arr] : {equal? {arr := 2} arr}} 25) "false")


; built-in functions

(check-equal? (top-interp '{* 1 2} 100) "2")
(check-equal? (top-interp '{/ 6 2} 100) "3")
(check-equal? (top-interp '{- 1 2} 100) "-1")
(check-equal? (top-interp '{<= 1 2} 100) "true")
(check-equal? (top-interp '{<= 3 2} 100) "false")
(check-equal? (top-interp '{equal? 1 1} 100) "true")
(check-equal? (top-interp '{equal? 2 1} 100) "false")
(check-equal? (top-interp '{equal? "a" "a"} 100) "true")
(check-equal? (top-interp '{equal? "b" "a"} 100) "false")
(check-equal? (top-interp '{equal? 1 "1"} 100) "false")

; general
(check-equal? (top-interp '{{blam (x) {+ x 1}} 2} 100) "3")
(check-equal? (top-interp '{{blam (x y) {+ x y}} 2 4} 100) "6")
(check-equal? (top-interp '{with [{blam (x) {+ x 1}} as f] : {f 2}} 100) "3")
(check-equal? (top-interp '{with [{blam (x) {+ x 1}} as f] : {f 2}} 100) "3")
(check-equal? (top-interp '{with [{blam (x) {+ x 1}} as f] [{blam (y) 3} as g] : {f {g "string"}}} 100) "4")
(check-equal? (top-interp '{with [{blam (x) {equal? x "5"}} as f] : {{f "5"} ? 5 else: 6}} 100) "5")
(check-equal? (top-interp '{with [{blam (x) {equal? x "5"}} as f] : {{f "4"} ? 5 else: 6}} 100) "6")
(check-equal? (top-interp '{equal? {equal? 1 2} {equal? 2 3}} 100) "true")
(check-equal? (top-interp '{equal? {<= 1 2} {<= 4 3}} 100) "false")
(check-equal? (top-interp '{blam (x) {+ x 1}} 100) "#<procedure>")
(check-equal? (top-interp '{{<= 1 2} ? "yes" else: "no"} 100) "\"yes\"")
(check-equal? (top-interp '{{blam (x) {x 3 4}} +} 100) "7")
(check-equal? (top-interp '{{blam (x) x} +} 100) "#<primop>")
(check-equal?
 (top-interp '{{blam (seven) {seven}}
               {{blam (minus) (blam () {minus (+ 3 10) (* 2 3)})} {blam (x y) {+ x (* -1 y)}}}} 100) "7")
(check-equal? (top-interp '{{blam (three) {three}} {{blam (x) {blam () {x 1 2}}} {blam (x y) {+ x y}}}} 100) "3")
(check-equal? (top-interp '{{blam () {equal? 2 2}}} 100) "true")


; errors
(check-exn (regexp (regexp-quote "user-error"))
           (lambda () (top-interp '{error "checking user calling an error"} 100)))
(check-exn (regexp (regexp-quote "error"))
           (lambda () (top-interp '{error} 100)))
(check-exn (regexp (regexp-quote "+"))
           (lambda () (top-interp '{+ 3} 100)))
(check-exn (regexp (regexp-quote "+"))
           (lambda () (top-interp '{+ 5 "hello"} 100)))
(check-exn (regexp (regexp-quote "-"))
           (lambda () (top-interp '{- 3} 100)))
(check-exn (regexp (regexp-quote "-"))
           (lambda () (top-interp '{- 5 "hello"} 100)))
(check-exn (regexp (regexp-quote "*"))
           (lambda () (top-interp '{* 3 5 2} 100)))
(check-exn (regexp (regexp-quote "*"))
           (lambda () (top-interp '{* 3 "hello"} 100)))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 5 2} 100)))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 0} 100)))
(check-exn (regexp (regexp-quote "/"))
           (lambda () (top-interp '{/ 3 "hello"} 100)))
(check-exn (regexp (regexp-quote "<="))
           (lambda () (top-interp '{<= 3 "hello"} 100)))
(check-exn (regexp (regexp-quote "<="))
           (lambda () (top-interp '{<= 3 5 2} 100)))
(check-exn (regexp (regexp-quote "equal?"))
           (lambda () (top-interp '{equal? 3 3 3} 100)))
(check-exn (regexp (regexp-quote "desugar-id"))
           (lambda () (top-interp '{with [{blam (x) {+ x 1}} as f f] : {f 2}} 100)))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (top-interp '{with [{blam (?) {+ x 1}} as f] : {f 2}} 100)))
(check-exn (regexp (regexp-quote "lookup"))
           (lambda () (top-interp '{equal? f 3 3} 100)))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{{blam (x) {+ x 1}} 3 4} 100)))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{3 4} 100)))
(check-exn (regexp (regexp-quote "interp"))
           (lambda () (top-interp '{3 ? 4 else: 5} 100)))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (top-interp '{#f} 100)))
(check-exn (regexp (regexp-quote "parse-id"))
           (lambda () (top-interp '{{blam ({x}) {+ x 1}} 3} 100)))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (top-interp '{blam (x x) 3} 100)))
(check-exn (regexp (regexp-quote "parse"))
           (lambda () (parse '{with [(blam () 3) as z] [9 as z] : (z)})))







