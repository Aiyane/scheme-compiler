;; author: aiyane
#|
Program   ----> Expr
Expr      ----> uvar
            |   (quote datum)
            |   (if Expr Expr Expr)
            |   (begin Expr* Expr)
            |   (lambda (uvar*) Expr)
            |   (let ([uvar Expr]*) Expr)
            |   (letrec ([uvar Expr]*) Expr)
            |   (set! uvar Expr)
            |   (primitive Expr*)
            |   (Expr Expr*)

A datum is an immediate, pair of datums, or vector of datums; and an immediate is a boolean, a xnum, or the empty list.
Where uvar is symbol.n, n >= 0
      fixnum is an exact integer
      primitives are void (zero arguments); car, cdr, vector-length,
      make-vector, boolean?, fixnum?, null?, pair?, procedure?, box,
      unbox, box?, vector? (one argument); *, +, -, cons, vector-ref,
      <, <=, =, set-box!, >=, >, eq?, set-car!, set-cdr!
      (two arguments); and vector-set! (three arguments).
|#

(load "utils/match.ss")
(load "utils/helpers.ss")
(load "utils/driver.ss")
(load "utils/wrapper.ss")

(define pred-prims '(< <= = >= > boolean? eq? fixnum? null? pair? vector? procedure? box?))
(define effect-prims '(set-car! set-cdr! vector-set! procedure-set! set-box!))
(define value-prims '(* + - car cdr cons make-vector vector-length vector-ref
                      void procedure-ref procedure-code make-procedure box unbox))
(define prims '(< <= = >= > boolean? eq? fixnum? null? pair? vector?
                set-car! set-cdr! vector-set! * + - car cdr cons
                make-vector vector-length vector-ref void procedure?
                procedure-set! procedure-ref procedure-code make-procedure
                box? set-box! box unbox))

;; to verify that program conforms to the subset of scheme grammar
(define-who parse-scheme
  (define primitives
    '((+ . 2) (- . 2) (* . 2) (<= . 2) (< . 2) (= . 2)
      (>= . 2) (> . 2) (boolean? . 1) (car . 1) (cdr . 1)
      (cons . 2) (eq? . 2) (fixnum? . 1) (make-vector . 1)
      (null? . 1) (pair? . 1) (procedure? . 1) (set-car! . 2)
      (set-cdr! . 2) (vector? . 1) (vector-length . 1)
      (vector-ref . 2) (vector-set! . 3) (void . 0) (procedure-set! . 3)
      (procedure-ref . 2) (procedure-code . 1) (make-procedure . 2)
      (box? . 1) (set-box! . 2) (box . 1) (unbox . 1)))

  ;; constant ----> fixnum | () | #t | #f
  (define constant?
    (lambda (x)
      (or (memq x '(#t #f ()))
          (and (integer? x) (exact? x) (fixnum-range? x)))))

  ;; A datum is an immediate, pair of datums, or vector of datums;
  ;; and an immediate is a boolean, a xnum, or the empty list.
  (define datum?
    (lambda (x)
      (or (constant? x)
          (if (pair? x)
              (and (datum? (car x)) (datum? (cdr x)))
              (and (vector? x) (andmap datum? (vector->list x)))))))

  (define check-unique
    (lambda (uvar* result* expr)
      (cond
        [(null? uvar*) #t]
        [(memq (car uvar*) result*) (errorf who "duplicate variables in expression ~s" expr)]
        [else (check-unique (cdr uvar*) (cons (car uvar*) result*) expr)])))

  (define generate
    (lambda (uvar)
      `(,uvar . ,(unique-name uvar))))

  (define adjust
    (lambda (bind* env)
      (cond
        [(null? bind*) env]
        [else (let* ([x (caar bind*)]
                     [res (assq x env)])
                (if res
                    (adjust (cdr bind*) (cons (car bind*) (remq res env)))
                    (adjust (cdr bind*) (cons (car bind*) env))))])))
  ;; Expr      ----> constant
  ;;             |   var
  ;;             |   (quote datum)
  ;;             |   (if Expr Expr)
  ;;             |   (if Expr Expr Expr)
  ;;             |   (and Expr*)
  ;;             |   (or Expr*)
  ;;             |   (not Expr)
  ;;             |   (begin Expr* Expr)
  ;;             |   (lambda (var*) Expr+)
  ;;             |   (let ([var Expr]*) Expr+)
  ;;             |   (letrec ([var Expr]*) Expr+)
  ;;             |   (set! var Expr)
  ;;             |   (primitive Expr*)
  ;;             |   (Expr Expr*)
  (define Expr
    (lambda (env)
      (lambda (x)
        (match x
          [,x (guard (symbol? x))
            (cond
              [(assq x env) (cdr (assq x env))]
              [else (errorf who "unbound variable ~s" x)])]
          [,x (guard (constant? x)) `(quote ,x)]
          [(quote ,datum) (guard (not (assq 'quote env)))
            (cond
              [(datum? datum) `(quote ,datum)]
              [else (errorf who "error in Datum Expression ~s" datum)])]
          [(not ,[x]) (guard (not (assq 'not env)))
            `(if ,x (quote #f) (quote #t))]
          [(if ,[test] ,[conseq]) (guard (not (assq 'if env)))
            `(if ,test ,conseq (void))]
          [(if ,[test] ,[conseq] ,[alt]) (guard (not (assq 'if env)))
            `(if ,test ,conseq ,alt)]
          [(and ,x* ...) (guard (not (assq 'and env)))
            (cond
              [(null? x*) (quote #t)]
              [(= (length x*) 1) ((Expr env) (car x*))]
              [else `(if ,((Expr env) (car x*))
                         ,((Expr env) `(and ,(cdr x*) ...))
                         (quote #f))])]
          [(or ,x* ...) (guard (not (assq 'or env)))
            (cond
              [(null? x*) (quote #f)]
              [(= (length x*) 1) ((Expr env) (car x*))]
              [else (let ([temp (unique-name 't)])
                      `(let ([,temp ,((Expr env) (car x*))])
                         (if ,temp
                             ,temp
                             ,((Expr env) `(or ,(cdr x*) ...)))))])]
          [(begin ,[expr*] ... ,[expr]) (guard (not (assq 'begin env)))
            `(begin ,expr* ... ,expr)]
          [(lambda (,uvar* ...) ,tail* ...) (guard (not (assq 'lambda env)))
            (if (null? tail*)
                (errorf who "Tail Expression in ~s must have atleast one value" x)
                (let* ([_ (check-unique uvar* '() x)]
                       [bind* (map generate uvar*)]
                       [new-env (adjust bind* env)]
                       [new-tail (map (Expr new-env) tail*)])
                  `(lambda ,(map cdr bind*) ,(make-begin new-tail))))]
          [(let ([,uvar* ,[expr*]] ...) ,tail* ...) (guard (not (assq 'let env)))
            (if (null? tail*)
                (errorf who "Tail Expression in ~s must have atleast one value" x)
                (let* ([_ (check-unique uvar* '() x)]
                       [bind* (map generate uvar*)]
                       [new-env (adjust bind* env)]
                       [new-tail (map (Expr new-env) tail*)])
                  `(let ([,(map cdr bind*) ,expr*] ...)
                     ,(make-begin new-tail))))]
          [(letrec ([,uvar* ,expr*] ...) ,tail* ...) (guard (not (assq 'letrec env)))
            (if (null? tail*)
                (errorf who "Tail Expression in ~s must have atleast one value" x)
                (let* ([_ (check-unique uvar* '() x)]
                       [bind* (map generate uvar*)]
                       [new-env (adjust bind* env)]
                       [new-expr* (map (Expr new-env) expr*)]
                       [new-tail* (map (Expr new-env) tail*)])
                  `(letrec ([,(map cdr bind*) ,new-expr*] ...)
                     ,(make-begin new-tail*))))]
          [(set! ,x ,y) (guard (not (assq 'set! env)))
            (cond
              [(and (symbol? x) (assq x env))
                `(set! ,(cdr (assq x env)) ,((Expr env) y))]
              [else (errorf who "Either ~s is not a symbol or ~s is not bound" x x)])]
          [(,prim ,[x*] ...) (guard (and (assq prim primitives)
                                         (not (assq prim env))))
            (if (= (length x*) (cdr (assq prim primitives)))
                `(,prim ,x* ...)
                (errorf who "Invalid arguments to primitive ~s" prim))]
          [(,[x] ,[x*] ...) `(,x ,x* ...)]
          [,other (errorf who "Invalid Expression ~s" other)]))))
  ;; Program   ----> Expr
  (lambda (program)
    ((Expr '()) program)))

;; pass: convert-complex-datum
(define-who convert-complex-datum
  (lambda (x)
    (define binds '())
    (define convert-const
      (lambda (x)
        (match x
          [() (quote '())]
          [(,[a] . ,[d]) `(cons ,a ,d)]
          [#(,[x*] ...)
           (let* ([tmp (unique-name 't)]
                  [len (length x*)]
                  [sets (let loop ([ls x*] [n 0])
                          (cond
                            [(null? ls) '()]
                            [else (cons `(vector-set! ,tmp (quote ,n) ,(car ls))
                                        (loop (cdr ls) (add1 n)))]))])
             `(let ([,tmp (make-vector (quote ,len))])
                (begin ,@sets ,tmp)))]
          [,x `(quote ,x)])))
    (define Expr
      (lambda (x)
        (match x
          [(quote ,imm) (guard (or (number? imm) (boolean? imm) (null? imm)))
           `(quote ,imm)]
          [(quote ,imm)
           (let ([new-var (unique-name 'u)]
                 [const (convert-const imm)])
             (set! binds (cons `(,new-var ,const) binds))
             new-var)]
          [(,[x*] ...) x*]
          [,o o])))
    (let ([x* (Expr x)])
      `(let ,binds ,x*))))

;; pass: uncover-assigned
(define-who uncover-assigned
  (define Expr
    (lambda (x)
      (match x
        [,uvar (guard (uvar? uvar)) (values uvar '())]
        [(if ,[t t-b] ,[c c-b] ,[a a-b])
          (values `(if ,t ,c ,a) (union t-b c-b a-b))]
        [(quote ,datum) (values `(quote ,datum) '())]
        [(begin ,[expr* e-b] ... ,[tail t-b])
          (values `(begin ,expr* ... ,tail) (union (apply append e-b) t-b))]
        [(lambda (,uvar* ...) ,[tail t-b])
          (let ([assigned-uvars (intersection t-b `(,uvar* ...))])
            (values `(lambda (,uvar* ...) (assigned (,assigned-uvars ...) ,tail))
              t-b))]
        [(letrec ([,uvar* ,[expr* e-b]] ...) ,[tail t-b])
          (let ([assigned-uvars (intersection uvar* (union t-b (apply append e-b)))])
            (values `(letrec ([,uvar* ,expr*] ...)
                      (assigned (,assigned-uvars ...)
                        ,tail))
              (difference (union t-b (apply append e-b)) uvar*)))]
        [(let ([,uvar* ,[expr* e-b]] ...) ,[tail t-b])
          (let ([assigned-uvars (intersection uvar* (union t-b (apply append e-b)))])
            (values `(let ([,uvar* ,expr*] ...)
                      (assigned (,assigned-uvars ...)
                        ,tail))
              (difference (union t-b (apply append e-b)) uvar*)))]
        [(set! ,x ,[rhs r-b])
          (values `(set! ,x ,rhs)
            (union `(,x) r-b))]
        [(,prim ,[expr* e-b] ...) (guard (memq prim prims))
          (values `(,prim ,expr* ...) (apply append e-b))]
        [(,[expr e-b] ,[rem* r-b] ...)
          (values `(,expr ,rem* ...) (union (apply append r-b) e-b))])))
  (lambda (x)
    (let-values ([(expr _) (Expr x)])
      expr)))


;; pass: purify-letrec
(define-who purify-letrec
  (define lambda-expr?
    (lambda (x)
      (match x
        [(lambda (,uvar* ...) ,x) #t]
        [,x #f])))
  (define seperate-lambdas
    (lambda (assign* uvar* expr*)
      (cond
        [(and (null? assign*) (null? uvar*)) #t]
        [(and (null? assign*) (lambda-expr? (car expr*)))
          (seperate-lambdas assign* (cdr uvar*) (cdr expr*))]
        [else #f])))
  ;; x.6 -> x.7
  (define generate-uvar
    (lambda (uvar)
      (unique-name (string->symbol (extract-root uvar)))))
  (define generate-set!
    (lambda (x y)
      `(set! ,x ,y)))
  (lambda (x)
    (match x
      [,uvar (guard (uvar? uvar)) uvar]
      [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
      [(quote ,datum) `(quote ,datum)]
      [(begin ,[expr*] ... ,[tail]) `(begin ,expr* ... ,tail)]
      [(lambda (,uvar* ...) (assigned (,assign* ...) ,[tail]))
        `(lambda (,uvar* ...)
          (assigned (,assign* ...) ,tail))]
      [(let ([,uvar* ,[expr*]] ...) (assigned (,assign* ...) ,[tail]))
        `(let ([,uvar* ,expr*] ...)
          (assigned (,assign* ...) ,tail))]
      [(set! ,x ,[rhs]) `(set! ,x ,rhs)]
      [(,prim ,[expr*] ...) (guard (memq prim prims))
        `(,prim ,expr* ...)]
      [(letrec ([,uvar* ,[expr*]] ...) (assigned (,assign* ...) ,[tail]))
        (let ([is-pure (seperate-lambdas assign* uvar* expr*)])
          (if (eq? is-pure #t)
              `(letrec ([,uvar* ,expr*] ...)
                ,(if (null? assign*)
                      `(,tail ...)
                      `(assigned (,assign* ...) ,tail)))
              (let* ([new* (map generate-uvar uvar*)]
                     [new-set! (map generate-set! uvar* new*)])
                `(let ([,uvar* (void)] ...)
                  (assigned (,uvar* ...)
                    (begin 
                      (let ([,new* ,expr*] ...)
                        (assigned ()
                          ,(make-begin new-set!)))
                      ,tail))))))]
      [(,[expr] ,[rem*] ...) `(,expr ,rem* ...)])))

;; pass: convert-assignments
(define-who convert-assignments
  (define make-bindings
    (lambda (as* bd*)
      (let loop ([bd* bd*] [bdo* '()] [env* '()])
        (cond
         [(null? bd*) (values (reverse bdo*) (reverse env*))]
         [(and (not (pair? (car bd*))) (memq (car bd*) as*)) ; lambda 语句
          (let ([new (unique-name (car bd*))])
            (loop (cdr bd*)
                  (cons new bdo*)
                  (cons `(,(car bd*) (box ,new)) env*)))]
         [(and (pair? (car bd*)) (memq (caar bd*) as*)) ; let 语句
          (let ([new (unique-name (caar bd*))])
            (loop (cdr bd*)
                  (cons `[,new ,(cadar bd*)] bdo*)
                  (cons `[,(caar bd*) (box ,new)] env*)))]
         [else
          (loop (cdr bd*) (cons (car bd*) bdo*) env*)]))))
  (define convert
    (lambda (x env)
      (match x
        [(letrec ([,uvar* ,[expr*]] ...) ,[body])
         `(letrec ([,uvar* ,expr*] ...) ,body)]
        [(let ([,uvar* ,[expr*]] ...) (assigned (,as* ...) ,expr))
         (let-values ([(bd* env*) (make-bindings as* `([,uvar* ,expr*] ...))])
           `(let ,bd* (let ,env* ,(convert expr (append as* env)))))]
        [(lambda (,uvar* ...) (assigned (,as* ...) ,body))
         (let-values ([(bd* env*) (make-bindings as* `(,uvar* ...))])
           `(lambda ,bd* (let ,env* ,(convert body (append as* env)))))]
        [(begin ,[ef*] ...)
         `(begin ,ef* ...)]
        [(if ,[t] ,[c] ,[a])
         `(if ,t ,c ,a)]
        [(set! ,x ,[v])
         (if (memq x env) `(set-box! ,x ,v) `(set! ,x ,v))]
        [(,[f] ,[x*] ...)
         `(,f ,x* ...)]
        [,x (if (memq x env) `(unbox ,x) x)])))
  (lambda (x)
    (convert x '())))


;; pass: optimize-direct-call
(define optimize-direct-call
  (lambda (x)
    (match x
      [(quote ,imm)
       `(quote ,imm)]
      [(if ,[t] ,[c] ,[a])
       `(if ,t ,c ,a)]
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [((lambda (,fml* ...) ,[body]) ,[x*] ...)
       `(let ([,fml* ,x*] ...) ,body)]
      [(let ([,x* ,[v*]] ...) ,[e])
       `(let ([,x* ,v*] ...) ,e)]
      [(letrec ([,uvar* (lambda (,fml** ...) ,[x*])] ...) ,[e])
       `(letrec ([,uvar* (lambda (,fml** ...) ,x*)] ...) ,e)]
      [(,[f] ,[x*] ...)
       `(,f ,x* ...)]
      [,x x])))

;; pass: remove-anonymous-lambda
(define-who remove-anonymous-lambda
  (define Expr
    (lambda (flag)
      (lambda (x)
        (match x
          [,x (guard (uvar? x)) x]
          [(if ,[(Expr 1) -> t] ,[(Expr 1) -> c] ,[(Expr 1) -> a])
            `(if ,t ,c ,a)]
          [(quote ,im) `(quote ,im)]
          [(let ([,uvar* ,[(Expr 0) -> expr*]] ...) ,[(Expr 1) -> tail])
            `(let ([,uvar* ,expr*] ...) ,tail)]
          [(begin ,[(Expr 1) -> expr*] ... ,[(Expr flag) -> expr])
            `(begin ,expr* ... ,expr)]
          [(letrec ([,uvar* (lambda (,param* ...) ,[(Expr 1) -> tail*])] ...) ,[(Expr flag) -> tail])
            `(letrec ([,uvar* (lambda (,param* ...) ,tail*)] ...) ,tail)]
          [(lambda (,uvar* ...) ,[(Expr 1) -> x])
            (if (eq? flag 0)
                `(lambda (,uvar* ...) ,x)
                (let ([anon-var (unique-name 'anon)])
                  `(letrec ([,anon-var (lambda (,uvar* ...) ,x)]) ,anon-var)))]
          [(,prim ,[(Expr 1) -> x*] ...) (guard (memq prim prims))
            `(,prim ,x* ...)]
          [(,[(Expr 1) -> x] ,[(Expr 1) -> y*] ...) `(,x ,y* ...)]))))
  (lambda (x)
    ((Expr 0) x)))

;; pass: sanitize-binding-forms
(define-who sanitize-binding-forms
  (define map2
    (lambda (fn x* y*)
      (cond
        [(null? x*) '()]
        [else (let ([res (fn (car x*) (car y*))]
                    [rest (map2 fn (cdr x*) (cdr y*))])
                (if (null? res)
                    rest
                    (cons res rest)))])))
  (define lambda-expr?
      (lambda (expr)
          (match expr
            [(lambda (,uvar* ...) ,x) #t]
            [,x #f])))
  (lambda (x)
    (match x
      [(let ([,uvar* ,[expr*]] ...) ,[tail])
        (let ([functions (map2 (lambda (uvar expr)
                                  (if (lambda-expr? expr)
                                      `(,uvar ,expr)
                                      '()))
                            uvar* expr*)]
              [variables (map2 (lambda (uvar expr)
                                  (if (lambda-expr? expr)
                                      '()
                                      `(,uvar ,expr)))
                            uvar* expr*)])
          (cond
            [(and (null? variables) (null? functions)) tail]
            [(null? functions) `(let ,variables ,tail)]
            [(null? variables) `(letrec ,functions ,tail)]
            [else `(letrec ,functions (let ,variables ,tail))]))]
      [(,[x] ,[y*] ...) `(,x ,y* ...)]
      [,o o])))

;; pass: uncover-free
(define-who uncover-free
  (define Expr
    (lambda (x)
      (match x
        [,uvar (guard (uvar? uvar))
         (values uvar `(,uvar))]
        [(lambda (,param* ...) ,[tail free])
         (let ([free* (difference free param*)])
           (values `(lambda ,param* (free ,free* ,tail)) free*))]
        [(letrec ([,uvar* ,[body* free*]] ...) ,[tail free])
         (values `(letrec ([,uvar* ,body*] ...) ,tail)
                 (difference (union free (apply union free*)) uvar*))]
        [(let ([,uvar* ,[expr* free*]] ...) ,[tail free])
         (values `(let ([,uvar* ,expr*] ...) ,tail)
                 (difference (union free (apply union free*)) uvar*))]
        [(,[val* free*] ...) (values val* (apply union free*))]
        [,o (values o '())])))
  (lambda (x)
    (let-values ([(expr _) (Expr x)])
      expr)))

;; pass: convert-closures
(define-who convert-closures
  (define Expr
    (lambda (x)
      (match x
        [(letrec (,[Body -> expr* local-closure*] ...) ,[tail])
         `(letrec ,expr* (closures ,local-closure* ,tail))]
        [,uvar (guard (uvar? uvar)) uvar]
        [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [(quote ,im) `(quote ,im)]
        [(begin ,[expr*] ...) `(begin ,expr* ...)]
        [(let ([,uavr* ,[expr*]] ...) ,[tail]) `(let ([,uavr* ,expr*] ...) ,tail)]
        [(,prim ,[expr*] ...) (guard (memq prim prims)) `(,prim ,expr* ...)]
        [(,[f] ,[rand*] ...)
         (if (uvar? f)
             `(,f ,f ,rand* ...)
             (let ([t (unique-name 't)])
               `(let ([,t ,f])
                  (,t ,t ,rand* ...))))])))
  (define Body
    (lambda (x)
      (match x
        [[,uvar (lambda (,param* ...) (free (,free* ...) ,[Expr -> body]))]
         (let ([label (unique-label uvar)]
               [func-ptr (unique-name 'fp)])
           (values `[,label (lambda (,func-ptr ,param* ...)
                             (bind-free (,func-ptr ,free* ...) ,body))]
                   `(,uvar ,label ,free* ...)))])))
  (lambda (x)
    (Expr x)))

;; pass: optimize-known-call
(define-who optimize-known-call
  (define lookup
    (lambda (x s)
      (cond
        [(assq x s) => cadr]
        [else #f])))
  (define optimize
    (lambda (cls)
      (lambda (x)
        (match x
          [(letrec ((,l* (lambda (,fml* ...) (bind-free (,x* ...) ,expr*))) ...)
             (closures ([,uvar* ,lc* ,fv* ...] ...) ,expr))
           (let* ([cls^ (append `([,uvar* ,lc*] ...) cls)]
                  [expr*^ (map (optimize cls^) expr*)]
                  [expr^ ((optimize cls^) expr)])
             `(letrec ((,l* (lambda (,fml* ...) (bind-free (,x* ...) ,expr*^))) ...)
                (closures ([,uvar* ,lc* ,fv* ...] ...) ,expr^)))]
          [(let ([,uvar* ,[expr*]] ...) ,[expr])
           `(let ([,uvar* ,expr*] ...) ,expr)]
          [(begin ,[e*] ...) `(begin ,e* ...)]
          [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
          [(quote ,imm) `(quote ,imm)]
          [(,prim ,[x*] ...) (guard (memq prim prims))
           `(,prim ,x* ...)]
          [(,[f] ,[f^] ,[x*] ...)
           `(,(or (lookup f cls) f) ,f^ ,x* ...)]
          [,x x]))))
  (lambda (x)
    (if *enable-optimize-known-call*
        ((optimize '()) x)
        x)))

;; pass: introduce-procedure-primitives
(define introduce-procedure-primitives
  (lambda (x)
    (define locate
      (lambda (x ls)
        (cond
         [(null? ls) #f]
         [(eq? x (car ls)) 0]
         [(locate x (cdr ls)) => add1]
         [else #f])))
    (define locate-fv
      (lambda (cpv)
        (lambda (x)
          (cond
           [(locate x (cdr cpv)) =>
            (lambda (i) `(procedure-ref ,(car cpv) ',i))]
           [else x]))))
    (define make-set!
      (lambda (x)
        (define make
          (lambda (x n)
            (match x
              [(,fuvar ,label) '()]
              [(,fuvar ,label ,free ,free* ...)
               (cons `(procedure-set! ,fuvar ',n ,free)
                     (make `(,fuvar ,label ,free* ...) (add1 n)))])))
        (make x 0)))
    (define intro
      (lambda (bd)
        (lambda (x)
          (match x
            [(letrec ((,label* ,[(intro '(dummy)) -> lam*]) ...) ,[expr])
             `(letrec ([,label* ,lam*] ...) ,expr)]
            [(lambda (,fptr ,x* ...)
               (bind-free (,fptr ,free* ...) ,[(intro `(,fptr ,@free*)) -> expr]))
             `(lambda (,fptr ,x* ...) ,expr)]
            [(let ([,uvar* ,[expr*]] ...) ,[expr])
             `(let ([,uvar* ,expr*] ...) ,expr)]
            [(begin ,[e*] ...) `(begin ,e* ...)]
            [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
            [(quote ,imm) `(quote ,imm)]
            [(closures ([,fuvar* ,label* ,[free*] ...] ...) ,[expr])
             (let ([length* (map length free*)])
               `(let ([,fuvar* (make-procedure ,label* ',length*)] ...)
                  (begin
                    ,(map make-set! `([,fuvar* ,label* ,free* ...] ...)) ... ...
                    ,expr)))]
            [(,f ,[x*] ...) (guard (or (memq f prims) (label? f)))
             `(,f ,x* ...)]
            [(,[f] ,[f],[x*] ...)
             `((procedure-code ,f) ,f ,x* ...)]
            [,x ((locate-fv bd) x)]))))
    ((intro '(dummy)) x)))

;; pass: lift-letrec
(define-who lift-letrec
  (lambda (x)
    (define definitions '())
    (define Expr
      (lambda (x)
        (match x
          [(letrec ([,label* (lambda (,fml** ...) ,[body*])] ...) ,[tail])
           (set! definitions
             (append definitions `([,label* (lambda (,fml** ...) ,body*)] ...)))
           tail]
          [(,[val*] ...) val*]
          [,o o])))
    (let ([tail (Expr x)])
      `(letrec ,definitions ,tail))))

;; pass: normalize-context
(define-who normalize-context
  (define make-nopless-begin
    (lambda (x*)
      (let ([x* (remove '(nop) x*)])
        (if (null? x*)
            '(nop)
            (make-begin x*)))))
  (define Effect
    (lambda (x)
      (match x
        [,x (guard (uvar? x)) '(nop)]
        [(if ,[Pred -> t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
        [(let ([,uvar* ,[Value -> value*]] ...) ,[tail])
         `(let ([,uvar* ,value*] ...) ,tail)]
        [(,prim ,[Value -> val*] ...) (guard (memq prim effect-prims))
         `(,prim ,val* ...)]
        [(,prim ,val* ...) (guard (or (memq prim value-prims) (memq prim pred-prims)))
         '(nop)]
        [(,[Value -> val] ,[Value -> val*] ...) `(,val ,val* ...)])))
  (define Pred
    (lambda (x)
      (match x
        [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [x (guard (label? x)) '(true)]
        [(begin ,[Effect -> ef*] ... ,[ef])
         (make-nopless-begin `(,ef* ... ,ef))]
        [(let ([,uvar* ,[Value -> val*]] ...) ,[tail])
         `(let ([,uvar* ,val*] ...) ,tail)]
        [(,prim ,[Value -> val*] ...) (guard (memq prim value-prims))
         `(if (eq? (,prim ,val* ...) '#f) (false) (true))]
        [(,prim ,[Value -> val*] ...) (guard (memq prim pred-prims))
         `(,prim ,val* ...)]
        [(,prim ,[Value -> val*] ...) (guard (memq prim effect-prims))
         (make-nopless-begin `((,prim ,val* ...) (true)))]
        [(,[Value -> val*] ...) `(if (eq? ,val* '#f) (false) (true))]
        [,o `(if (eq? ,o '#f) (false) (true))])))
  (define Value
    (lambda (x)
      (match x
        [(if ,[Pred -> t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [(begin ,[Effect -> ef*] ... ,[ef]) (make-nopless-begin `(,ef* ... ,ef))]
        [(,prim ,[val*] ...) (guard (memq prim pred-prims))
         `(if (,prim ,val* ...) '#t '#f)]
        [(,prim ,[val*] ...) (guard (memq prim effect-prims))
         (make-nopless-begin `((,prim ,val* ...) (void)))]
        [(,[val*] ...) val*]
        [,o o])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Value -> val*])] ...) ,[Value -> tail])
       `(letrec ([,label* (lambda (,fml** ...) ,val*)] ...) ,tail)])))

(define handler-prims
  (lambda (x)
    (match x
      [(void) $void]   
      [(eq? ,v1 ,v2) `(= ,v1 ,v2)]
      [(null? ,v) `(= ,v ,$nil)]
      [(set-car! ,v1 ,v2) `(mset! ,v1 ,(- disp-car tag-pair) ,v2)]
      [(set-cdr! ,v1 ,v2) `(mset! ,v1 ,(- disp-cdr tag-pair) ,v2)]
      [(car ,v1) `(mref ,v1 ,(- disp-car tag-pair))]
      [(cdr ,v1) `(mref ,v1 ,(- disp-cdr tag-pair))]
      [(boolean? ,v1)
       `(= (logand ,v1 ,mask-boolean) ,tag-boolean)]
      [(vector? ,v1)
       `(= (logand ,v1 ,mask-vector) ,tag-vector)]
      [(fixnum? ,v1)
       `(= (logand ,v1 ,mask-fixnum) ,tag-fixnum)]
      [(pair? ,v1)
       `(= (logand ,v1 ,mask-pair) ,tag-pair)]
      [(vector-length ,v1)
       `(mref ,v1 ,(- disp-vector-length tag-vector))]
      [(* ,v1 ,v2)
       (cond
         [(integer? v1) `(* ,(sra v1 shift-fixnum) ,v2)]
         [(integer? v2) `(* ,v1 ,(sra v2 shift-fixnum))]
         [else `(* ,v1 (sra ,v2 ,shift-fixnum))])]
      [(vector-ref ,v1 ,v2)
       (if (integer? v2)
           `(mref ,v1 ,(+ (- disp-vector-data tag-vector) v2))
           `(mref ,v1 (+ ,(- disp-vector-data tag-vector) ,v2)))]
      [(vector-set! ,v1 ,v2 ,v3)
       (if (integer? v2)
           `(mset! ,v1 ,(+ (- disp-vector-data tag-vector) v2) ,v3)
           `(mset! ,v1 (+ ,(- disp-vector-data tag-vector) ,v2) ,v3))]   
      [(cons ,v1 ,v2)
       (let ([x (unique-name 't)]
             [y (unique-name 't)]
             [z (unique-name 't)])
         `(let ([,x ,v1]
                [,y ,v2]
                [,z (+ (alloc ,size-pair) ,tag-pair)])
           (begin
             (mset! ,z ,(- disp-car tag-pair) ,x)
             (mset! ,z ,(- disp-cdr tag-pair) ,y)
             ,z)))]
      [(make-vector ,size)
       (let ([vector (unique-name 't)])
         (if (integer? size)
             `(let ([,vector (+ (alloc ,(+ disp-vector-data size)) ,tag-vector)])
               (begin
                 (mset! ,vector ,(- disp-vector-length tag-vector) ,size)
                 ,vector))
             `(let ([,vector (+ (alloc (+ ,disp-vector-data ,size)) ,tag-vector)])
               (begin
                 (mset! ,vector ,(- disp-vector-length tag-vector) ,size)
                 ,vector))))]
      [(procedure? ,v1)
       `(= (logand ,v1 ,mask-procedure) ,tag-procedure)]   
      [(procedure-set! ,v1 ,v2 ,v3)
       (if (integer? v2)
           `(mset! ,v1 ,(+ (- disp-procedure-data tag-procedure) v2) ,v3)
           `(mset! ,v1 (+ ,(- disp-procedure-data tag-procedure) ,v2) ,v3))]   
      ;; TODO: size 没有实际用到？
      [(make-procedure ,func ,size)
       (let ([size-var (unique-name 't)])
         (if (integer? size)
             `(let ([,size-var (+ (alloc ,(+ disp-procedure-data size)) ,tag-procedure)])
                (begin
                  (mset! ,size-var ,(- disp-procedure-code tag-procedure) ,func)
                  ,size-var))
             `(let ([,size-var (+ (alloc (+ ,disp-procedure-code ,size)) ,tag-procedure)])
                (begin
                  (mset! ,size-var ,(- disp-procedure-code tag-procedure) ,func)
                  ,size-var))))]
      [(procedure-code ,v1)
       `(mref ,v1 ,(- disp-procedure-code tag-procedure))]
      [(procedure-ref ,v1 ,v2)
       (if (integer? v2)
           `(mref ,v1 ,(+ (- disp-procedure-data tag-procedure) v2))
           `(mref ,v1 (+ ,(- disp-procedure-data tag-procedure) ,v2)))]
      [(box? ,v1)
       `(= (logand ,e ,mask-box) ,tag-box)]
      [(box ,v1)
       (let ([x (unique-name 't)]
             [y (unique-name 't)])
         `(let ([,x ,v1]
                [,y (+ (alloc ,size-box) ,tag-box)])
           (begin
             (mset! ,y ,(- tag-box) ,x)
             ,y)))]
      [(set-box! ,v1 ,v2)
       `(mset! ,v1 ,(- tag-box) ,v2)]
      [(unbox ,v1)
       `(mref ,v1 ,(- tag-box))]
      [,o o])))

;; pass: specify-representation
(define-who specify-representation
  (define Expr
    (lambda (x)
      (match x
        [(quote #t) $true]
        [(quote #f) $false]
        [(quote ()) $nil]
        [(quote ,t) (guard (integer? t)) (ash t shift-fixnum)]
        [(,prim ,[val*] ...) (guard (memq prim prims)) (handler-prims `(,prim ,val* ...))]
        [(,[val*] ...) val*]
        [,o o])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,uvar** ...) ,[Expr -> val*])] ...) ,[Expr -> val])
       `(letrec ([,label* (lambda (,uvar** ...) ,val*)] ...) ,val)])))

;; pass: uncover-locals
(define-who uncover-locals
  (define Expr
    (lambda (x)
      (match x
        [(let ([,new-uvar* ,[uvar*]] ...) ,[val])
         (apply union new-uvar* val uvar*)]
        [(,[v*] ...) (apply union v*)]
        [,o '()])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,uvar** ...) ,[bd*])] ...) ,[bd])
       `(letrec ([,label* (lambda (,uvar** ...) ,bd*)] ...) ,bd)]
      [,o `(locals ,(Expr o) ,o)])))

;; pass: remove-let
(define-who remove-let
  (define Expr
    (lambda (x)
      (match x
        [(let ([,new-uvar* ,[uvar*]] ...) ,[tail])
         (make-begin `((set! ,new-uvar* ,uvar*) ... ,tail))]
        [(,[v*] ...) v*]
        [,o o])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,uvar** ...) ,[bd*])] ...) ,[bd])
       `(letrec ([,label* (lambda (,uvar** ...) ,bd*)] ...) ,bd)]
      [(locals ,uvar* ,[Expr -> tail])
       `(locals ,uvar* ,tail)])))

(define max-unique-name-count
  (lambda (ls)
    (let ([num (unique-name-count)])
      (map (lambda (v)
             (let ([n (string->number (extract-suffix v))])
               (when (> n num)
                 (set! num n))))
           ls)
      (unique-name-count num))))

;; to verify that program conforms to the subset of scheme grammar
(define-who verify-uil
  (define verify-x-list
    (lambda (x* x? what)
      (max-unique-name-count x*)
      (let loop ([x* x*] [idx* '()])
        (unless (null? x*)
          (unless (x? (car x*))
            (errorf who "invalid ~s ~s found" what (car x*)))
          (let ([idx (extract-suffix (car x*))])
            (when (member idx idx*)
              (errorf who "non-unique ~s suffix ~s found" what idx))
            (loop (cdr x*) (cons idx idx*)))))))
  ;; Triv    ----> uvar | int | label
  (define Triv
    (lambda (label* uvar*) 
      (lambda (t)
        (unless (or (label? t) (uvar? t) 
                    (and (integer? t) (exact? t))) 
          (errorf who "invalid Triv ~s" t))
        (when (and (integer? t) (exact? t))
          (unless (int64? t)
            (errorf who "integer out of 64-bit range ~s" t)))
        (when (uvar? t) 
          (unless (memq t uvar*) 
            (errorf who "invalid Triv ~s" t))) 
        (when (label? t) 
          (unless (memq t label*) 
            (errorf who "unbound label ~s" t))) 
        t)))
  ;; Value   ----> Triv
  ;;           |   (alloc Value)
  ;;           |   (mref Value Value)
  ;;           |   (binop Value Value)
  ;;           |   (Value Value*)
  ;;           |   (if Pred Value Value)
  ;;           |   (begin Effect* Value)
  (define Value
    (lambda (label* uvar*)
      (lambda (val)
        (match val
          [(alloc ,[(Value label* uvar*) -> mem-size]) (void)]
          [(mref ,[(Value label* uvar*) -> base] ,[(Value label* uvar*) -> offset]) (void)]
          [(if ,[(Pred label* uvar*) -> test] ,[conseq] ,[altern]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[val]) (void)]
          [(sra ,[x] ,y) (unless (uint6? y)
                            (errorf who "invalid sra operand ~s" y))]
          [(,binop ,[x] ,[y]) (guard (memq binop '(+ - * logand logor sra))) (void)]
          [(,[rator] ,[rand*] ...) (void)]
          [,[(Triv label* uvar*) -> tr] (void)]))))
  ;; Effect  ----> (nop)
  ;;           |   (set! uvar Value)
  ;;           |   (mset! Value Value Value) 
  ;;           |   (Value Value*)
  ;;           |   (if Pred Effect Effect)
  ;;           |   (begin Effect* Effect)
  (define Effect
    (lambda (label* uvar*) 
      (lambda (ef) 
        (match ef
          [(nop) (void)]
          [(set! ,var ,[(Value label* uvar*) -> val])
            (unless (memq var uvar*)
              (errorf who "assignment to unbound var ~s" var))]
          [(mset! ,[(Value label* uvar*) -> base] ,[(Value label* uvar*) -> offset] ,[(Value label* uvar*) -> val]) (void)]
          [(begin ,[ef] ,[ef*] ...) (void)]
          [(if ,[(Pred label* uvar*) -> pred] ,[ef-a] ,[ef-b]) (void)]
          [(,[(Value label* uvar*) -> rator] ,[(Value label* uvar*) -> rand*] ...) (void)]
          [,other (errorf who "invalid Effect ~s" other)]))))
  ;; Pred    ----> (true)
  ;;           |   (false)
  ;;           |   (relop Value Value)
  ;;           |   (if Pred Pred Pred)
  ;;           |   (begin Effect* Pred)
  (define Pred
    (lambda (label* uvar*)
      (lambda (pred)
        (match pred
          [(true) (void)]
          [(false) (void)]
          [(if ,[pred-a] ,[pred-b] ,[pred-c]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[pd]) (void)]
          [(,relop ,[(Value label* uvar*) -> x] 
                  ,[(Value label* uvar*) -> y])
            (unless (memq relop '(= < <= > >=))
              (errorf who "invalid predicate operator ~s" relop))]
          [,other (errorf who "invalid Pred ~s" other)]))))
  ;; Tail    ----> Triv
  ;;           |   (alloc Value)
  ;;           |   (mref Value Value)
  ;;           |   (binop Value Value)
  ;;           |   (Value Value*)
  ;;           |   (if Pred Tail Tail)
  ;;           |   (begin Effect* Tail)
  (define Tail
    (lambda (label* uvar*) 
      (lambda (tail)
        (match tail
          [(alloc ,[(Value label* uvar*) -> mem-size]) (void)]
          [(mref ,[(Value label* uvar*) -> base] ,[(Value label* uvar*) -> offset]) (void)]
          [(if ,[(Pred label* uvar*) -> pred] ,[tail-a] ,[tail-b]) (void)]
          [(begin ,[(Effect label* uvar*) -> ef*] ... ,[tail]) (void)]
          [(sra ,[(Value label* uvar*) -> x] ,y)
            (unless (uint6? y)
              (errorf who "invalid sra operand ~s" y))]
          [(,binop ,[(Value label* uvar*) -> x] ,[(Value label* uvar*) -> y])
            (guard (memq binop '(+ - * logand logor sra))) (void)]
          [(,[(Value label* uvar*) -> rator]
            ,[(Value label* uvar*) -> rand*] ...) 
            (void)]
          [,[(Triv label* uvar*) -> triv] (void)]))))
  ;; Body    ----> (locals (uvar*) Tail)
  (define Body
    (lambda (label*)
      (lambda (body fml*)
        (match body
          [(locals (,local* ...) ,tail)
            (let ([uvar* `(,fml* ... ,local* ...)])
              (verify-x-list uvar* uvar? 'uvar)
              ((Tail label* uvar*) tail))]
          [,other (errorf who "invalid Body ~s" other)]))))
  ;; Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
  (lambda (program) 
    (match program 
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
        (verify-x-list label* label? 'label)
        (map (lambda (fml*) (verify-x-list fml* uvar? 'formal)) fml**)
        (for-each (Body label*) `(,bd* ... ,bd) `(,fml** ... ()))] 
      [,other (errorf who "invalid Program ~s" other)]) 
    program))

(define find-max
  (lambda (fvs)
    (let ([num -1])
      (map (lambda (fv)
             (when (frame-var? fv)
               (set! num (max num (frame-var->index fv)))))
           fvs)
      num)))

(define remove-nulls
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [(null? (car ls)) (remove-nulls (cdr ls))]
      [else (set-cons (car ls) (remove-nulls (cdr ls)))])))

(define resolve
  (lambda (not-type? lhs live* ct)
    (define add-ct!
      (lambda (var1 var2)
        (if (not (eq? var1 var2))
            (let ([a (assq var1 ct)])
              (if (not a)
                  (set! ct (cons `(var1 var2) ct))
                  (set-cdr! a (set-cons var2 (cdr a))))))))
    (when (uvar? lhs)
      (for-each
        (lambda (live) (add-ct! lhs live))
        live*))
    (for-each
      (lambda (live)
        (when (and (uvar? live)
                   (not (not-type? lhs)))
          (add-ct! live lhs)))
      live*)))

(define (index->new-frame-var _) (unique-name 'nfv)) 

;; pass: remove-complex-opera*
(define remove-complex-opera*
  (lambda (x)
    (define new-local* '())
    (define (new-t)
      (set! new-local* (cons (unique-name 't) new-local*))
      (car new-local*))
    (define trivial?
      (lambda (exp)
        (or (uvar? exp) (int64? exp) (label? exp)
            (memq exp '(+ - * logand logor sra = < <= > >= alloc mref mset!)))))
    (define make-trivial
      (lambda (arg)
        (if (trivial? arg)
            `(() . ,arg)
            (let ([new-var (new-t)])
              `(((set! ,new-var ,arg)) . ,new-var)))))
    (define Expr
      (lambda (x)
        (match x
          [(,v) (guard (memq v '(true false nop))) `(,v)]
          [(,kv ,[arg*] ...) (guard (memq kv '(begin if)))
           `(,kv ,arg* ...)]
          [(set! ,var ,[value])
           `(set! ,var ,value)]
          [(,[value] ,[value*] ...)
           (let ([trivial-tail (map make-trivial `(,value ,value* ...))])
             `(begin ,@(apply append (map car trivial-tail)) ,(map cdr trivial-tail)))]
          [,triv triv])))
    (define Body
      (lambda (bd)
        (set! new-local* '())
        (match bd
          [(locals (,local* ...) ,[Expr -> tail])
           `(locals (,local* ... ,new-local* ...) ,tail)])))
    (match x
      [(letrec ([,label* (lambda ,args* ,[Body -> bd*])] ...) ,[Body -> bd])
       `(letrec ([,label* (lambda ,args* ,bd*)] ...) ,bd)])))

;; pass: flatten-set!
(define-who flatten-set!
  (define new-local* '())
  (define (new-t)
    (let ([t (unique-name 't)])
      (set! new-local* (cons t new-local*)) t))
  (define make-flatten
    (lambda (v expr)
      (match expr
        [(begin ,[Expr -> ef*] ... ,[val])
         (make-begin `(,ef* ... ,val))]
        [(if ,[Expr -> pred] ,[conseq] ,[alt])
         `(if ,pred ,conseq ,alt)]
        ;; 这里直接返回了，没有再调用 Tail(make-flatten) 了
        [(alloc ,val)
         `(begin (set! ,v ,allocation-pointer-register)
                 (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,val)))]
        [,x `(set! ,v ,x)])))
  (define Expr
    (lambda (x)
      (match x
        [(begin ,[ef*] ... ,[tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[pred] ,[conseq] ,[alt])
         `(if ,pred ,conseq ,alt)]
        [(alloc ,val)
         (let ([t (new-t)])
           `(begin (set! ,t ,allocation-pointer-register)
                   (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,val)) ,t))]
        [(set! ,v ,expr)
         (make-flatten v expr)]
        [,o o])))
  (define Body
    (lambda (x)
      (set! new-local* '())
      (match x
        [(locals (,uvar* ...) ,[Expr -> tail])
         `(locals (,uvar* ... ,new-local* ...) ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda ,args* ,[Body -> bd*])] ...) ,[Body -> bd])
       `(letrec ([,label* (lambda ,args* ,bd*)] ...) ,bd)])))

;; pass: impose-calling-conventions
(define-who impose-calling-conventions
  (define new-frame-var** '())
  (define assign-parameters
    (lambda (val* idx->fv nfv-f)
      (let loop ([val* val*] [regs parameter-registers] [idx 0])
        (cond
          [(null? val*) '()]
          [(null? regs) (let ([fv (idx->fv idx)])
                          (unless (frame-var? fv) (nfv-f fv))
                          (cons fv (loop (cdr val*) '() (add1 idx))))]
          [else (cons (car regs) (loop (cdr val*) (cdr regs) idx))]))))
  (define Body
    (lambda (bd fml*)
      (set! new-frame-var** '())
      (let ([rp (unique-name 'rp)])
        (match bd 
          [(locals (,locals* ...) ,[(Expr index->frame-var rp) -> tail])
           (let ([assignments (assign-parameters fml* index->frame-var (lambda (nfv) nfv))])
             `(locals (,locals* ... ,rp ,fml* ... ,new-frame-var** ... ...)
               (new-frames (,new-frame-var** ...)
                 ,(make-begin
                    `((set! ,rp ,return-address-register)
                      (set! ,fml* ,assignments) ...
                      ,tail)))))]))))
  (define Expr
    (lambda (idx->fv rp)
      (lambda (x)
        (match x
          [(begin ,[(Expr index->new-frame-var '()) -> ef*] ... ,[(Expr index->frame-var rp) -> tail])
           `(begin ,ef* ... ,tail)]
          [(if ,[arg*] ...) `(if ,arg* ...)]
          [(set! ,uvar (,triv ,triv* ...)) (guard (or (uvar? triv) (label? triv)))
           (make-begin `(,((Expr idx->fv rp) `(,triv ,triv* ...)) (set! ,uvar ,return-value-register)))]
          [(,v ,arg* ...) (guard (memq v '(true false = < <= > >= nop set! mset!)))
           `(,v ,arg* ...)]
          [(,triv ,loc* ...) (guard (and (null? rp) (or (uvar? triv) (label? triv))))
           (let ([rp (unique-label 'rp)])
             `(return-point ,rp ,((Expr idx->fv rp) `(,triv ,loc* ...))))]
          [(,triv ,loc* ...) (guard (or (uvar? triv) (label? triv)))
           (let* ([new-frame-var* '()]
                  [assignments (assign-parameters loc* idx->fv
                                 (lambda (nfv) (set! new-frame-var* (append new-frame-var* `(,nfv)))))])
             (unless (null? new-frame-var*)
               (set! new-frame-var** (cons new-frame-var* new-frame-var**)))
             `(begin (set! ,assignments ,loc*) ...
                     (set! ,return-address-register ,rp)
                     (,triv ,return-address-register ,frame-pointer-register ,allocation-pointer-register ,@assignments)))]
          [,triv `(begin (set! ,return-value-register ,triv)
                         (,rp ,frame-pointer-register ,return-value-register ,allocation-pointer-register))]))))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
       `(letrec ([,label* (lambda () ,(map Body bd* fml**))] ...) ,(Body bd '()))])))

(define uncover-?-conflict
  (lambda (x not-type? t? live* t-live* f-live* ct return-point-f)
    (define Triv
      (lambda (x)
        (if (or (t? x) (uvar? x)) `(,x) '())))
    (match x
      [(true) t-live*]
      [(false) f-live*]
      [(begin) live*]
      [(begin ,ef* ... ,[live*])
       (uncover-?-conflict `(begin ,ef* ...) not-type? t? live* t-live* f-live* ct return-point-f)]
      [(if ,test ,[c-live*] ,[a-live*])
       (uncover-?-conflict test not-type? t? live* (union live* c-live*) (union live* a-live*) ct return-point-f)]
      [(nop) live*]
      [(set! ,lhs (,binop ,[Triv -> x-live*] ,[Triv -> y-live*]))
       (let ([new-live* (remq lhs live*)])
         (resolve not-type? lhs live* ct)
         (union x-live* y-live* new-live*))]
      [(set! ,lhs ,[Triv -> var*])
       (let ([new-live* (remq lhs live*)])
         (resolve not-type? lhs live* ct)
         (union var* new-live*))]
      [(mset! ,[Triv -> base] ,[Triv -> offset] ,[Triv -> value])
       (unless (null? base)
         (resolve not-type? base (union offset value live*) ct))
       (union base offset value live*)]
      [(return-point ,rp ,[new-live*])
       ;; Effect 调用会丢掉上下文，所以需要 union
       (return-point-f live*) (union live* new-live*)]
      [(,relop ,[Triv -> x-live*] ,[Triv -> y-live*]) (guard (memq relop '(= < <= > >=)))
       (remove-nulls (union x-live* y-live* t-live* f-live*))]
      [(,[Triv -> target*] ,[Triv -> live**] ...)
       (remove-nulls (union target* (apply append live**)))])))

;; pass: uncover-frame-conflict
(define-who uncover-frame-conflict
  (lambda (x)
    (match x
      [(locals (,uvar* ...) (new-frames (,nfv** ...) ,tail))
       (let ([ct (map list uvar*)] [call-live* '()])
         ; 在 return-point 时仍然 live 的集合就是 call-live 的
         (uncover-?-conflict tail register? frame-var? '() '() '() ct
           (lambda (live*) (set! call-live* (union call-live* live*))))
         (let ([spill* (filter uvar? call-live*)])
           `(locals (,(difference uvar* spill*) ...)
              (new-frames (,nfv** ...)
                (spills ,spill*
                  (frame-conflict ,ct
                    (call-live (,call-live* ...) ,tail)))))))]
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

(define k (length registers))

(define low-degree?
  (lambda (var ct)
    (< (num-conflicts var ct) k)))

(define num-conflicts
  (lambda (var ct)
    (length (cdr (assq var ct)))))

(define replace
  (lambda (allocations conflict-uvars)
    (map (lambda (uvar)
            (let ([reg (assq uvar allocations)])
              (if (eq? reg #f) uvar (cadr reg))))
      conflict-uvars)))

(define find-frame-homes
  (lambda (var* ct home*)
    (cond
      [(null? var*) home*]
      [else (let* ([current-var (car var*)]
                   [var* (remq current-var var*)]
                   [conflict-uvars (assq current-var ct)]
                   [conflict-entry (replace home* (cdr conflict-uvars))]
                   [max-val (find-max conflict-entry)]
                   [fv (index->frame-var (add1 max-val))])
              (find-frame-homes var* ct (cons `(,current-var ,fv) home*)))])))

;; pass: pre-assign-frame
(define-who pre-assign-frame
  (lambda (x)
    (match x
      [(locals (,local* ...)
         (new-frames (,nfv** ...)
           (spills (,spill* ...)
             (frame-conflict ,ct
               (call-live (,call-live* ...) ,tail)))))
       (let ([home* (find-frame-homes spill* ct '())])
         `(locals (,local* ...)
           (new-frames (,nfv** ...)
             (locate (,home* ...)
               (frame-conflict ,ct
                 (call-live (,call-live* ...) ,tail))))))]
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

;; pass: assign-new-frame
(define-who assign-new-frame
  (define do-assign
    (lambda (fs)
      (lambda (var*)
        (let f ([index fs] [ls var*] [rs '()])
          (let ([fv (index->frame-var index)])
            (cond
              [(null? ls) rs]
              [else (f (add1 index) (cdr ls) (cons `(,(car ls) ,fv) rs))]))))))
  (define Expr
    (lambda (fs)
      (lambda (x)
        (match x
          [(if ,[test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          [(begin ,[ef*] ...)
            `(begin ,ef* ...)]
          [(return-point ,rplab ,[tail])
           `(begin (set! ,frame-pointer-register (+ ,frame-pointer-register ,(ash fs align-shift)))
                   (return-point ,rplab ,tail)
                   (set! ,frame-pointer-register (- ,frame-pointer-register ,(ash fs align-shift))))]
          [,other other]))))
  (lambda (x)
    (match x
      [(locals (,local* ...)
         (new-frames (,nfv** ...)
           (locate (,home* ...)
             (frame-conflict ,ct
               (call-live (,call-live* ...) ,tail)))))
       (let ([fs (add1 (find-max (replace home* call-live*)))])
         `(locals ,(difference local* `(,nfv** ... ...))
            (ulocals ()
              (locate (,home* ... ,(map (do-assign fs) nfv**) ... ...)
                (frame-conflict ,ct ,((Expr fs) tail))))))]    
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

(define finalize-?-locations
  (lambda (env)
    (define V
      (lambda (v)
        (let ([entry (assq v env)])
          (if entry (cdr entry) v))))
    (lambda (expr)
      (match expr
        [(if ,[p] ,[t] ,[f])
         `(if ,p ,t ,f)]
        [(begin ,[ef*] ... ,[e])
         `(begin ,ef* ... ,e)]
        [(set! ,[V -> v] (,binop ,[V -> t-a] ,[V -> t-b]))
         `(set! ,v (,binop ,t-a ,t-b))]
        [(set! ,[V -> v] ,[V -> t])
         `(set! ,v ,t)]
        [(mset! ,[V -> base] ,[V -> offset] ,[V -> value])
         `(mset! ,base ,offset ,value)]
        [(return-point ,rp ,[tail])
         `(return-point ,rp ,tail)]    
        [(,[V -> t*] ...) t*]))))

;; pass: finalize-frame-locations
(define-who finalize-frame-locations
  (lambda (x)
    (match x
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
           (locate ([,uvar* ,loc*] ...)
             (frame-conflict ,ct ,[(finalize-?-locations (map cons uvar* loc*)) -> tail]))))
       `(locals ,local*
          (ulocals ,ulocal*
            (locate ([,uvar* ,loc*] ...)
              (frame-conflict ,ct ,tail))))]
      [(locate (,home* ...) ,tail) `(locate ,home* ,tail)]   
      [(letrec ([,label* (lambda () ,[bd*])] ...) ,[bd])
       `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)])))

;; pass: select-instructions
(define select-instructions
  (lambda (x)
    (define ulocal* '())
    (define (new-t)
      (let ([u (unique-name 't)])
        (set! ulocal* (cons u ulocal*)) u))
    (define operator^
      (lambda (op)
        (case op
          ['> '<]
          ['< '>]
          ['<= '>=]
          ['= '=])))
    ;; 遵循交换律的操作符
    (define commutative?
      (lambda (x)
        (memq x '(+ * logand logor))))
    (define complex-assignment-helper
      (lambda (exp)
        (match exp
          ;; Effect: (set! v1 (op v1 v2))
          ;;      -> op: (+ - logand logor)
          ;;        -> v1: register   v2: register
          ;;        -> v1: register   v2: uvar
          ;;        -> v1: register   v2: frame-var
          ;;        -> v1: register   v2: int32
          ;;        -> v1: uvar       v2: register
          ;;        -> v1: uvar       v2: uvar
          ;;        -> v1: uvar       v2: frame-var
          ;;        -> v1: uvar       v2: int32
          ;;        -> v1: frame-var  v2: register
          ;;        -> v1: frame-var  v2: uvar
          ;;        -> v1: frame-var  v2: int32
          ;;      -> op: (*)
          ;;        -> v1: register   v2: register
          ;;        -> v1: register   v2: uvar
          ;;        -> v1: register   v2: frame-var
          ;;        -> v1: register   v2: int32
          ;;        -> v1: uvar       v2: register
          ;;        -> v1: uvar       v2: uvar
          ;;        -> v1: uvar       v2: frame-var
          ;;        -> v1: uvar       v2: int32
          ;;      -> op: (sra)
          ;;        -> v1: register   v2: uint6
          ;;        -> v1: frame-var  v2: uint6
          ;;        -> v1: uvar       v2: uint6
          [(set! ,lhs (,binop ,lhs ,rhs)) (guard (memq binop '(+ - logand logor)))
           (if (and (frame-var? lhs) (or (frame-var? rhs) 
                                         (int64? rhs) 
                                         (label? rhs)))
               (let ([new-unspillable (new-t)])
                 `(begin (set! ,new-unspillable ,rhs)
                         (set! ,lhs (,binop ,lhs ,new-unspillable))))
               exp)]
          ;; lhs need to be assigned with new-unspillable-var
          [(set! ,lhs (,binop ,lhs ,rhs)) (guard (and (eq? binop '*) (frame-var? lhs)))
           (let* ([new-unspillable-var (new-t)]
                  [stmt `(set! ,new-unspillable-var (,binop ,new-unspillable-var ,rhs))])
             (let ([complex-assignment (complex-assignment-helper stmt)])
               `(begin (set! ,new-unspillable-var ,lhs)
                       ,complex-assignment
                       (set! ,lhs ,new-unspillable-var))))]
          [(set! ,lhs (,binop ,lhs ,rhs)) (guard (eq? binop 'sra)) exp]
          [(set! ,lhs (,binop ,lhs ,rhs)) (guard (or (uvar? lhs) (register? lhs))) exp])))
    (define simple-assignment
      (lambda (exp)
        (match exp
          ;; Effect: (set! v1 v2)
          ;;        -> v1: register   v2: register
          ;;        -> v1: register   v2: uvar
          ;;        -> v1: register   v2: frame-var
          ;;        -> v1: register   v2: int64
          ;;        -> v1: register   v2: label
          ;;        -> v1: uvar       v2: register
          ;;        -> v1: uvar       v2: uvar
          ;;        -> v1: uvar       v2: frame-var
          ;;        -> v1: uvar       v2: int64
          ;;        -> v1: uvar       v2: label
          ;;        -> v1: frame-var?   v2: register
          ;;        -> v1: frame-var?   v2: uvar
          ;;        -> v1: frame-var?   v2: int32
          [(set! ,x ,y) (guard (or (uvar? x) (register? x)))
           `(set! ,x ,y)]
          [(set! ,x ,y) (guard (frame-var? x))
           (if (or (frame-var? y) (label? y))
               (let ([new-unspillable (new-t)])
                 `(begin (set! ,new-unspillable ,y) (set! ,x ,new-unspillable)))
               `(set! ,x ,y))])))
    (define select-mref
      (lambda (lhs base offset)
        ;; Effect: (set! lhs (mref v1 v2))
        ;;      -> op: (mref)
        ;;        -> v1: uvar       v2: uvar
        ;;        -> v1: uvar       v2: register
        ;;        -> v1: uvar       v2: int32
        ;;        -> v1: register   v2: uvar
        ;;        -> v1: register   v2: register
        ;;        -> v1: register   v2: int32
        (let ([set* '()])
          (unless (or (uvar? offset)
                      (register? offset)
                      (int32? offset))
            (let ([u (new-t)])
              (set! set* (cons `(set! ,u ,offset) set*))
              (set! offset u)))
          (unless (or (uvar? base)
                      (register? base))
            (let ([u (new-t)])
              (set! set* (cons `(set! ,u ,base) set*))
              (set! base u)))
          `(begin ,@set* (set! ,lhs (mref ,base ,offset))))))
    (define select-mset!
      (lambda (base offset value)
        ;; Effect: (mset! v1 v2 v3)
        ;;       -> v1: uvar       v2: uvar
        ;;       -> v1: uvar       v2: register
        ;;       -> v1: uvar       v2: int32
        ;;       -> v1: register   v2: uvar
        ;;       -> v1: register   v2: register
        ;;       -> v1: register   v2: int32
        (let ([set* '()])
          (unless (or (uvar? offset)
                      (register? offset)
                      (int32? offset))
            (let ([u (new-t)])
              (set! set* (cons `(set! ,u ,offset) set*))
              (set! offset u)))
          (unless (or (uvar? base)
                      (register? base))
            (let ([u (new-t)])
              (set! set* (cons `(set! ,u ,base) set*))
              (set! base u)))
          `(begin ,@set* (mset! ,base ,offset ,value)))))
    (define Body
      (lambda (x)
        (match x
          [(locals (,local* ...)
             (ulocals (,orig-ulocal* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,[Expr -> tail]))))
           `(locals ,local*
              (ulocals (,orig-ulocal* ... ,ulocal* ...)
                (locate ,home*
                  (frame-conflict ,ct ,tail))))]
          [(locate (,home* ...) ,tail)
           `(locate ,home* ,tail)])))
    (define Expr
      (lambda (x)
        (match x
          [(begin ,[ef*] ... ,[tail])
           (make-begin `(,ef* ... ,tail))]
          [(if ,[pred] ,[conseq] ,[alt])
           `(if ,pred ,conseq ,alt)]
          [(return-point ,rp ,[tail])
           `(return-point ,rp ,tail)]
          [(mset! ,base ,offset ,value)
           (cond
             [(or (uvar? value) (register? value) (integer? value)) (select-mset! base offset value)]
             [(frame-var? value)
              (let ([u (new-t)])
                (make-begin `((set! ,u ,value) 
                              ,(select-mset! base offset u) 
                              (set! ,value ,u))))]
             [(label? value)
              (let ([u (new-t)])
                (make-begin `((set! ,u ,value) 
                              ,(select-mset! base offset u))))])]
          [(set! ,lhs (mref ,base ,offset))
           (cond
             [(or (uvar? lhs) (register? lhs)) (select-mref lhs base offset)]
             [(frame-var? lhs)
              (let ([u (new-t)])
                (make-begin `((set! ,u ,lhs)
                              ,(select-mref u base offset)
                              (set! ,lhs ,u))))]
             [(label? lhs)
              (let ([u (new-t)])
                (make-begin `((set! ,u ,lhs)
                              ,(select-mref u base offset))))])]
          [(set! ,lhs (,binop ,rhs1 ,rhs2))
           (cond
             [(eq? lhs rhs1) (complex-assignment-helper `(set! ,lhs (,binop ,rhs1 ,rhs2)))]
             [(and (commutative? binop) (eq? lhs rhs2))
              (complex-assignment-helper `(set! ,lhs (,binop ,rhs2 ,rhs1)))]
             [(eq? lhs rhs2)
              (let* ([new-unspillable-var (new-t)]
                     [stmt `(set! ,new-unspillable-var (,binop ,new-unspillable-var ,rhs2))])
                (let ([complex-assignment (complex-assignment-helper stmt)])
                  `(begin (set! ,new-unspillable-var ,rhs1)
                          ,complex-assignment
                          (set! ,lhs ,new-unspillable-var))))]
             [else
               ;; eg: (set! a (+ b c))
               ;;     -> (begin
               ;;     ->   (set! a b)
               ;;     ->   (set! a (+ a c)))
               ;; 上面是错误的, 因为此时 c 与 a 有冲突, 但原语句是没有冲突的, 所以改为如下
               ;; (begin
               ;;   (set! t.1 b)
               ;;   (set! t.1 (+ t.1 c))
               ;;   (set! a t.1))
               (let ([new-unspillable (new-t)])
                 `(begin (set! ,new-unspillable ,rhs1)
                         (set! ,new-unspillable (,binop ,new-unspillable ,rhs2))
                         (set! ,lhs ,new-unspillable)))])]
          [(set! ,x ,y) (simple-assignment `(set! ,x ,y))]
          ;; Pred: (op v1 v2)
          ;;       -> op: (= < <= > >=)
          ;;         -> v1: register     v2: register
          ;;         -> v1: register     v2: uvar
          ;;         -> v1: register     v2: frame-var
          ;;         -> v1: register     v2: int32
          ;;         -> v1: uvar         v2: register
          ;;         -> v1: uvar         v2: uvar
          ;;         -> v1: uvar         v2: frame-var
          ;;         -> v1: uvar         v2: int32
          ;;         -> v1: frame-var    v2: register
          ;;         -> v1: frame-var    v2: uvar
          ;;         -> v1: frame-var    v2: int32
          [(,relop ,triv1 ,triv2) (guard (memq relop '(= < <= > >=)))
           (cond
             [(or (uvar? triv1) (register? triv1))
              `(,relop ,triv1 ,triv2)]
             [(and (frame-var? triv1) (not (frame-var? triv2)))
              `(,relop ,triv1 ,triv2)]
             ;; (< 3 x.5) -> (> x.5 3)
             [(and (int32? triv1) (or (register? triv2)
                                      (uvar? triv2)
                                      (frame-var? triv2)))
              `(,(operator^ relop) ,triv2 ,triv1)]
             [(or (and (frame-var? triv1) (frame-var? triv2))
                  (int32? triv2))
              (let ([new-unspillable (new-t)])
                `(begin (set! ,new-unspillable ,triv1)
                        (,relop ,new-unspillable ,triv2)))]
             [else (let ([u1 (new-t)] [u2 (new-t)])
                     `(begin (set! ,u1 ,triv1)
                             (set! ,u2 ,triv2)
                             (,relop ,u1 ,u2)))])]
          [,o o])))
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

;; pass: uncover-register-conflict
(define-who uncover-register-conflict
  (define Body
    (lambda (bd)
      (match bd
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate (,home* ...)
               (frame-conflict ,fv-ct ,tail))))
          (let ([ct (map list (append local* ulocal*))])
            (uncover-?-conflict tail frame-var? register? '() '() '() ct (lambda (live*) live*))
            `(locals ,local*
              (ulocals ,ulocal*
                (locate ,home*
                  (frame-conflict ,fv-ct
                    (register-conflict ,ct ,tail))))))]
        [(locate (,home* ...) ,tail) `(locate ,home* ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

;; pass: assign-registers
(define-who assign-registers
  (define pick-min
    (lambda (var degree var* ct)
      (cond
        [(null? var*) var]
        [(<= degree (num-conflicts (car var*) ct)) (pick-min var degree (cdr var*) ct)]
        [else (let* ([node (car var*)]
                     [degree^ (num-conflicts node ct)])
                (pick-min node degree^ (cdr var*) ct))])))
  (define find-homes
    (lambda (var* results)
      (lambda (ct)
        (if (null? var*)
            results
            (let ([var (car var*)] [current-var '()])
              (if (low-degree? var ct)
                  (set! current-var var)
                  (set! current-var (pick-min var (num-conflicts var ct) (cdr var*) ct)))
              (let* ([conflict-uvars (assq current-var ct)]
                     [conflict-entry (replace results (cdr conflict-uvars))]
                     [remaining-registers (difference registers conflict-entry)])
                (unless (null? remaining-registers) ; 存在寄存器不够的情况
                  (set! results (cons (list current-var (car remaining-registers)) results)))
                ((find-homes (remq current-var var*) results) ct)))))))
  (define Body
    (lambda (x)
      (match x
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate (,frame-home* ...)
               (frame-conflict ,fv-ct
                 (register-conflict ,[(find-homes (append local* ulocal*) '()) -> home*] ,tail)))))
         (let ([spill* (difference (append local* ulocal*) (map car home*))])
           (cond [(null? spill*)
                  `(locate (,frame-home* ... ,home* ...) ,tail)]
                 [else (let ([local* (difference local* spill*)])
                         `(locals ,local*
                            (ulocals ,ulocal*
                              (spills ,spill*
                                (locate ,frame-home*
                                  (frame-conflict ,fv-ct ,tail))))))]))]
        [(locate (,home* ...) ,tail) `(locate ,home* ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

(define-who everybody-home? 
  (define all-home? 
    (lambda (body) 
      (match body 
        [(locals (,local* ...) 
           (ulocals (,ulocal* ...) 
             (spills (,spill* ...) 
               (locate (,home* ...) 
                 (frame-conflict ,ct ,tail))))) #f] 
        [(locate (,home* ...) ,tail) #t] 
        [,x (errorf who "invalid Body ~s" x)]))) 
  (lambda (x) 
    (match x 
      [(letrec ([,label* (lambda () ,body*)] ...) ,body) 
        (andmap all-home? `(,body ,body* ...))]
      [,x (errorf who "invalid Program ~s" x)])))

;; pass: assign-frame
(define-who assign-frame
  (lambda (x)
    (match x
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
           (spills (,spill* ...)
             (locate (,home* ...)
               (frame-conflict ,ct ,tail)))))
        (let ([home* (find-frame-homes spill* ct home*)])
          `(locals ,local*
            (ulocals ,ulocal*
              (locate ,home*
                (frame-conflict ,ct ,tail)))))]
      [(locate (,home* ...) ,tail) `(locate ,home* ,tail)]   
      [(letrec ([,label* (lambda () ,[body*])] ...) ,[body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

;; pass: discard-call-live
(define-who discard-call-live
  (lambda (program)
    (match program
      [(begin ,[ef*] ...)
       `(begin ,ef* ...)]
      [(if ,[test] ,[conseq] ,[alt])
       `(if ,test ,conseq ,alt)]
      [(return-point ,rp ,[tail]) `(return-point ,rp ,tail)]
      [(locate ([,uvar* ,reg*] ...) ,[tail])
       `(locate ([,uvar* ,reg*] ...) ,tail)]
      [(letrec ([,label* (lambda () ,[bd*])] ...) ,[bd])
       `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)]
      [(,target ,live* ...) (guard (or (uvar? target)
                                       (label? target)
                                       (frame-var? target)))
       `(,target)]
      [,o o])))

;; pass: finalize-locations
(define-who finalize-locations
  (define Body
    (lambda (body)
      (match body
        [(locate ([,uvar* ,loc*] ...) ,tail)
         ((finalize-?-locations (map cons uvar* loc*)) tail)])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))

;; pass: expose-frame-var
(define-who expose-frame-var
  (lambda (program)
    (define fp-offset 0)
    (define V 
      (lambda (t)
        (if (frame-var? t)
            (make-disp-opnd frame-pointer-register 
              (- (ash (frame-var->index t) align-shift) fp-offset))
            t)))
    ; 强制正序, match 多项匹配并不是正序的
    (define Begin
      (lambda (t)
        (match t
          [() '()]
          [(,[Expr -> stmt] ,stmt* ...) `(,stmt ,(Begin stmt*) ...)])))
    (define Expr
      (lambda (t)
        (match t
          [(if ,[pred] ,[t] ,[f])
           `(if ,pred ,t ,f)]
          [(begin ,stmt* ...) `(begin ,(Begin stmt*) ...)]
          [(set! ,fp (+ ,fp ,n)) (guard (eq? fp frame-pointer-register))
           (set! fp-offset (+ fp-offset n))
           `(set! ,fp (+ ,fp ,n))]
          [(set! ,fp (- ,fp ,n)) (guard (eq? fp frame-pointer-register))
           (set! fp-offset (- fp-offset n))
           `(set! ,fp (- ,fp ,n))]
	  [(set! ,[V -> lhs] (mref ,base ,offset)) ; base offset 只能是 register 或 int32
	   (if (and (register? base) (int32? offset))
	       `(set! ,lhs ,(make-disp-opnd base offset))
	       `(set! ,lhs ,(make-index-opnd base offset)))]
          [(mset! ,base ,offset ,[V -> value]) ; base offset 只能是 register 或 int32
	   (if (and (register? base) (int32? offset))
	       `(set! ,(make-disp-opnd base offset) ,value) 
	       `(set! ,(make-index-opnd base offset) ,value))]
          [(set! ,[V -> var] (,binop ,[V -> triv-a] ,[V -> triv-b]))
           `(set! ,var (,binop ,triv-a ,triv-b))]
          [(set! ,[V -> var] ,[V -> triv])
           `(set! ,var ,triv)]
          [(return-point ,rp ,[tail])
           `(return-point ,rp ,tail)]
          [(,relop ,[V -> a] ,[V -> b])
           `(,relop ,a ,b)]
          [(,[V -> triv]) `(,triv)])))
    (match program
      [(letrec ([,label* (lambda () ,[Expr -> tail*])] ...) ,[Expr -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)])))

;; pass: expose-basic-blocks
(define expose-basic-blocks
  (lambda (program)
    (define binding* '())
    (define bind-func
      (lambda (label state)
        (set! binding* (cons `(,label (lambda () ,state)) binding*))))
    (define Effect*
      (lambda (ef* code)
        (match ef*
          [() (make-begin code)]
          [(,ef* ... ,ef) (Effect ef* ef code)])))
    (define Effect
      (lambda (before* expr after*)
        (match expr
          [(if ,pred ,conseq ,alt)
           (let ([c-label (unique-label 'c)]
                 [a-label (unique-label 'a)]
                 [j-label (unique-label 'j)])
             (bind-func c-label (Effect '() conseq `((,j-label))))
             (bind-func a-label (Effect '() alt `((,j-label))))
             (bind-func j-label (make-begin after*))
             (Effect* before* `(,((Expr c-label a-label) pred))))]
          [(return-point ,rp ,[(Expr '() '()) -> tail])
           (bind-func rp (make-begin after*))
           (Effect* before* (cdr tail))] ; tail 总是以 begin 开头
          [(begin ,ef* ...)
           (Effect* before* `(,(Effect* ef* after*)))]
          [(set! ,loc ,triv)
           (Effect* before* `(,expr ,@after*))]
          [(nop) (Effect* before* after*)])))
    (define Expr
      (lambda (t-label f-label)
        (lambda (expr)
          (match expr
            [(true) `(,t-label)]
            [(false) `(,f-label)]
            [(begin ,ef* ... ,[tail]) (Effect* ef* `(,tail))]
            [(if ,pred ,[c-state*] ,[a-state*])
             (let ([c-label (unique-label 'c)]
                   [a-label (unique-label 'a)])
               (bind-func c-label c-state*)
               (bind-func a-label a-state*)
               ((Expr c-label a-label) pred))]
            [(,relop ,v1 ,v2)
             `(if (,relop ,v1 ,v2) (,t-label) (,f-label))]
            [(,tail) `(,tail)]))))
    (match program
      [(letrec ([,label* (lambda () ,[(Expr '() '()) -> expr*])] ...) ,[(Expr '() '()) -> expr])
       `(letrec ([,label* (lambda () ,expr*)] ... ,@binding*) ,expr)])))

;; pass: optimize-jumps
(define-who optimize-jumps
  (lambda (x)
    (define assoc-list '())
    (define build-assoc-list
      (lambda (x)
        (match x
          [(,label (lambda () ,tail))
           (match tail
             [(,next-label) (guard (label? next-label))
              (let ([symbol (walk next-label)])
                (cond
                  [(eq? symbol label) ; 死循环
                   `((,label (lambda () ,tail)))]
                  [else (set! assoc-list (cons (cons label symbol) assoc-list))
                        '()]))]
             [,o `((,label (lambda () ,o)))])])))
    (define walk
      (lambda (sym)
        (cond
          [(null? assoc-list) sym]
          [(assq sym assoc-list) => (lambda (x) (walk (cdr x)))]
          [else sym])))
    (define Expr
      (lambda (x)
        (match x
          [(,[val*] ...) val*]
          [,x (guard (label? x)) (walk x)]
          [,o o])))
    (if *enable-optimize-jumps*
        (match x
          [(letrec (,[build-assoc-list -> def**] ...) ,tail)
           (Expr `(letrec (,def** ... ...) ,tail))])
        x)))

;; pass: flatten-program
(define-who flatten-program
  (define make-body
    (lambda (label* tail*)
      (match label*
        [() '()]
        [(,current ,rest* ...)
         (let ([current-exp `(,current ,@(Tail rest* (car tail*)))])
           `(,@current-exp ,@(make-body rest* (cdr tail*))))])))
  (define Tail
    (lambda (label* x)
      (match x
        [(if ,pred (,conseq) (,alt))
         (let ([next-label (or (null? label*) (car label*))])
           (cond
             [(eq? next-label conseq)
              `((if (not ,pred) (jump ,alt)))]
             [(eq? next-label alt)
              `((if ,pred (jump ,conseq)))]
             [else `((if ,pred (jump ,conseq)) (jump ,alt))]))]
        [(begin ,stmt* ...)
         (match (make-begin stmt*)
                [(begin ,effect* ... ,tail)
                 `(,effect* ... ,@(Tail label* tail))])]
        [(,triv) `((jump ,triv))])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
       `(code ,@(Tail label* tail) ,@(make-body label* tail*))])))

(define-who generate-x86-64
  (define Binop
    (lambda (op) 
      (case op
        [(+) 'addq] 
        [(-) 'subq] 
        [(*) 'imulq] 
        [(logand) 'andq] 
        [(logor) 'orq] 
        [(sra) 'sarq] 
        [(=) 'je] 
        [(<) 'jl] 
        [(<=) 'jle] 
        [(>) 'jg] 
        [(>=) 'jge])))
  (define inst->inst^ 
    (lambda (inst) 
      (case inst 
        [(je) 'jne] 
        [(jl) 'jge] 
        [(jle) 'jg] 
        [(jg) 'jle] 
        [(jge) 'jl])))
  (define State
    (lambda (stmt)
      (match stmt
        [(set! ,var1 (,op ,var1 ,opnd)) (emit (Binop op) opnd var1)]
        [(set! ,reg ,lbl) (guard (label? lbl)) (emit 'leaq lbl reg)]
        [(set! ,var ,opnd) (emit 'movq opnd var)]
        [(jump ,opnd) (emit-jump 'jmp opnd)]
        [(if (,op ,x ,y) (jump ,lbl))
         (emit 'cmpq y x)
         (emit-jump (Binop op) lbl)]
        [(if (not (,op ,x ,y)) (jump ,lbl))
         (emit 'cmpq y x)
         (emit-jump (inst->inst^ (Binop op)) lbl)]
        [,var (emit-label var)])))
  (define Prog
    (lambda (program)
      (match program
        [(code ,st* ...) (for-each State st*)])))
  (lambda (program)
    (emit-program (Prog program))))

(compiler-passes '(
  parse-scheme
  convert-complex-datum
  uncover-assigned
  purify-letrec
  convert-assignments
  optimize-direct-call
  remove-anonymous-lambda
  sanitize-binding-forms
  uncover-free
  convert-closures
  optimize-known-call
  introduce-procedure-primitives
  lift-letrec
  normalize-context
  specify-representation
  uncover-locals
  remove-let
  verify-uil
  remove-complex-opera*
  flatten-set!
  impose-calling-conventions
  uncover-frame-conflict
  pre-assign-frame
  assign-new-frame
  (iterate
    finalize-frame-locations
    select-instructions
    uncover-register-conflict
    assign-registers
    (break when everybody-home?)
    assign-frame)
  discard-call-live
  finalize-locations
  expose-frame-var
  expose-basic-blocks
  optimize-jumps
  flatten-program
  generate-x86-64
))
