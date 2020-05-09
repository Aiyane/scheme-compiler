;; author: aiyane
#|
Program   ----> Expr
Expr      ----> constant
            |   var
            |   (quote datum)
            |   (if Expr Expr)
            |   (if Expr Expr Expr)
            |   (and Expr*)
            |   (or Expr*)
            |   (not Expr)
            |   (begin Expr* Expr)
            |   (lambda (var*) Expr+)
            |   (let ([var Expr]*) Expr+)
            |   (letrec ([var Expr]*) Expr+)
            |   (set! var Expr)
            |   (primitive Expr*)
            |   (Expr Expr*)

• constant is #t, #f, (), or a fixnum;
• fixnum is an exact integer;
• datum is a constant, pair of datums, or vector of datums; and
• var is an arbitrary symbol.
|#

(load "utils/match.ss")
(load "utils/helpers.ss")
(load "utils/driver.ss")
(load "utils/wrapper.ss")

(define *enable-optimize-jumps* #t)
(define *enable-optimize-known-call* #t)
(define *enable-optimize-direct-call* #t)

(define primitives
  '((+ . 2) (- . 2) (* . 2) (<= . 2) (< . 2) (= . 2)
    (>= . 2) (> . 2) (boolean? . 1) (car . 1) (cdr . 1)
    (cons . 2) (eq? . 2) (fixnum? . 1) (make-vector . 1)
    (null? . 1) (pair? . 1) (procedure? . 1) (set-car! . 2)
    (set-cdr! . 2) (vector? . 1) (vector-length . 1)
    (vector-ref . 2) (vector-set! . 3) (void . 0) (procedure-set! . 3)
    (procedure-ref . 2) (procedure-code . 1) (make-procedure . 2)))
(define pred-prims
  '((< . 2) (<= . 2) (= . 2) (>= . 2) (> . 2) (boolean? . 1) (procedure? . 1)
    (eq? . 2) (fixnum? . 1) (null? . 1) (pair? . 1) (vector? . 1)))
(define effect-prims
  '((set-car! . 2) (set-cdr! . 2) (vector-set! . 3) (procedure-set! . 3)))
(define value-prims
  '((* . 2) (+ . 2) (- . 2) (car . 1) (cdr . 1) (cons . 2)
    (make-vector . 1) (vector-length . 1) (vector-ref . 2) (void . 0)
    (procedure-ref . 2) (procedure-code . 1) (make-procedure . 2)))

(define find-max
  (lambda (ls)
    (cond
      [(null? (cdr ls)) (car ls)]
      [else (max (car ls) (find-max (cdr ls)))])))

(define remove-nulls
  (lambda (ls)
    (cond
      [(null? ls) '()]
      [(null? (car ls)) (remove-nulls (cdr ls))]
      [else (set-cons (car ls) (remove-nulls (cdr ls)))])))


(define-who parse-scheme
  (define constant?
    (lambda (x)
      (or (memq x '(#t #f ()))
          (and (integer? x) (exact? x) (fixnum-range? x)))))

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

  (lambda (program)
    ((Expr '()) program)))

;; pass: convert-complex-datum
(define-who convert-complex-datum
  (define binds '())
  (define vector-make
    (lambda (ls num tmp)
      (cond
        [(null? ls) '()]
        [(pair? (car ls))
          (let ([lst (handle-list (car ls))])
            (cons `(vector-set! ,tmp (quote ,num) ,lst) (vector-make (cdr ls) (add1 num) tmp)))]
        [(vector? (car ls))
          (let* ([vect (handle-vector (car ls))])
            (cons `(vector-set! ,tmp (quote ,num) ,vect) (vector-make (cdr ls) (add1 num) tmp)))]
        [else (cons `(vector-set! ,tmp (quote ,num) (quote ,(car ls))) (vector-make (cdr ls) (add1 num) tmp))])))
  (define handle-vector
    (lambda (x)
      (let* ([tmp (unique-name 't)]
             [len (vector-length x)]
             [ls (vector->list x)]
             [result (vector-make ls 0 tmp)])
        `(let ([,tmp (make-vector (quote ,len))])
           ,(make-begin `(,@result ,tmp))))))
  (define handle-list
    (lambda (x)
      (cond
        [(null? x) (quote '())]
        [(and (not (pair? x))
              (not (vector? x)))
          `(quote ,x)]
        [(vector? x) (handle-vector x)]
        [(pair? x) `(cons ,(handle-list (car x)) ,(handle-list (cdr x)))])))
  (define make-expression
    (lambda (x)
      (cond
        [(pair? x) (handle-list x)]
        [(vector? x) (handle-vector x)])))
  (define Datum
    (lambda (x)
      (cond
        [(memq x '(#t #f ())) `(quote ,x)]
        [(and (integer? x) (exact? x))
          (unless (fixnum-range? x)
            (errorf who "integer ~s is out of fixnum range" x))
          `(quote ,x)]
        [else (let ([new-var (unique-name 'u)])
                (set! binds (cons `(,new-var ,(make-expression x)) binds))
                new-var)])))
  (define Expr
    (lambda (x)
      (match x
        [,x (guard (uvar? x)) x]
        [(quote ,[Datum -> datum]) datum]
        [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [(begin ,[expr*] ... ,[expr]) `(begin ,expr* ... ,expr)]
        [(lambda (,uvar* ...) ,[body]) `(lambda (,uvar* ...) ,body)]
        [(let ([,uvar* ,[expr*]] ...) ,[tail])
          `(let ([,uvar* ,expr*] ...) ,tail)]
        [(letrec ([,uvar* ,[expr*]] ...) ,[tail])
          `(letrec ([,uvar* ,expr*] ...) ,tail)]
        [(set! ,x ,[expr]) `(set! ,x ,expr)]
        [(,prim ,[expr*] ...) (guard (assq prim primitives))
          `(,prim ,expr* ...)]
        [(,[expr] ,[expr*] ...) `(,expr ,expr* ...)])))
  (lambda (x)
    (set! binds '())
    (let ([expr (Expr x)])
      `(let ,binds ,expr))))


;; pass: uncover-assigned
#| output:
Program   ----> Expr
Expr      ----> uvar
            |   (quote datum)
            |   (if Expr Expr Expr)
            |   (begin Expr* Expr)
            |   (lambda (uvar*) (assigned (assign*) Expr))
            |   (let ([uvar Expr]*) (assigned (assign*) Expr))
            |   (letrec ([uvar Expr]*) (assigned (assign*) Expr))
            |   (set! uvar Expr)
            |   (primitive Expr*)
            |   (Expr Expr*)
|#
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
        [(,prim ,[expr* e-b] ...) (guard (assq prim primitives))
          (values `(,prim ,expr* ...) (apply append e-b))]
        [(,[expr e-b] ,[rem* r-b] ...)
          (values `(,expr ,rem* ...) (union (apply append r-b) e-b))])))
  (lambda (x)
    (let-values ([(expr _) (Expr x)])
      expr)))


;; pass: purify-letrec
;; if e isnot a lambda expr.
;; (letrec ((x e) ...)
;;  (assigned (x! ...)
;;    body)) ->
;;  (let ((x (void)) ...)
;;    (assigned (x ...)
;;      (begin
;;        (let ((t e) ...)
;;          (assigned ()
;;            (begin (set! x t) ...)))
;;        body)))
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
      [(,prim ,[expr*] ...) (guard (assq prim primitives))
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
;; (assigned (x . . .) expr) ====> (let ((x (cons t (void))) . . .) expr)
;; (set! x e) ====> (set-car! x e)
;; x ====> (car x)
;; (let ([x.3 '10] [y.1 '11] [z.2 '12])
;;   (assigned (x.3 z.2)
;;     (begin
;;       (set! x.3 (+ x.3 y.1))
;;       (set! z.2 (* y.1 '2))
;;       (cons y.1 z.2)))) ====>
;; (let ([x.5 '10] [y.1 '11] [z.4 '12])
;;   (let ([x.3 (cons x.5 (void))] [z.2 (cons z.4 (void))])
;;     (begin
;;       (set-car! x.3 (+ (car x.3) y.1))
;;       (set-car! z.2 (* y.1 '2))
;;       (cons y.1 (car z.2)))))
(define-who convert-assignments
  ;; x.6 -> x.7
  (define generate-uvar
    (lambda (uvar)
      (unique-name (string->symbol (extract-root uvar)))))
  (define make-let
    (lambda (new assign)
      `(,assign (cons ,new (void)))))
  (define make-outer-lets
    (lambda (uvar* assgin-new* expr*)
      (cond
        [(null? uvar*) '()]
        [else
          (let ([uvar (car uvar*)])
            (cond
              [(assq uvar assgin-new*) => 
                (lambda (assgin-new)
                  (let ([expr (cadr (assq uvar expr*))])
                    (cons `(,(cadr assgin-new) ,expr) (make-outer-lets (cdr uvar*) assgin-new* expr*))))]
              [else (cons (assq uvar expr*) (make-outer-lets (cdr uvar*) assgin-new* expr*))]))])))
  (define Expr
    (lambda (assigned*)
      (lambda (x)
        (match x
          [,uvar (guard (uvar? uvar))
            (if (memq uvar assigned*)
                `(car ,uvar)
                uvar)]
          [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
          [(quote ,datum) `(quote ,datum)]
          [(begin ,[expr*] ... ,[tail])
            `(begin ,expr* ... ,tail)]
          [(lambda (,uvar* ...) (assigned (,assign* ...) ,[(Expr (union assigned* assign*)) -> tail]))
            (if (null? assign*)
                `(lambda (,uvar* ...) ,tail)
                (let* ([new* (map generate-uvar assign*)]
                        [new-let* (map make-let new* assign*)])
                  `(lambda (,new* ...)
                    (let ,new-let* ,tail))))]
          ;; letrec 中只存在函数赋值，所以不用变换
          [(letrec ([,uvar* ,[expr*]] ...) 
             (assigned (,assign* ...) ,[(Expr (union assigned* assign*)) -> tail]))
            `(letrec ([,uvar* ,expr*] ...) ,tail)]
          [(letrec ([,uvar* ,[expr*]] ...) ,[tail])
            `(letrec ([,uvar* ,expr*] ...) ,tail)]
          [(let ([,uvar* ,[expr*]] ...)
             (assigned (,assign* ...) ,[(Expr (union assign* assigned*)) -> tail]))
            (if (null? assign*)
                `(let ([,uvar* ,expr*] ...) ,tail)
                (let* ([new* (map generate-uvar assign*)]
                       [new-let* (map make-let new* assign*)]
                       [outer-let* (make-outer-lets uvar* `([,assign* ,new*] ...) `([,uvar* ,expr*] ...))])
                  `(let ,outer-let*
                    (let ,new-let* ,tail))))]
          [(set! ,x ,[rhs]) `(set-car! ,x ,rhs)]
          [(,prim ,[expr*] ...) (guard (assq prim primitives))
            `(,prim ,expr* ...)]
          [(,[expr] ,[rem*] ...) `(,expr ,rem* ...)]))))
  (lambda (x)
    ((Expr '()) x)))

;; pass: optimize-direct-call
;; ((lambda (x.1) x.1) '3) ====> (let ([x.1 '3]) x.1)
(define-who optimize-direct-call
  (define lambda-expr?
    (lambda (expr)
      (match expr
        [(lambda (,uvar* ...) ,x) #t]
        [,x #f])))
  (define convert-lambda
    (lambda (fn param*)
      (match fn
        [(lambda (,uvar* ...) ,[Expr -> x])
          (if (= (length uvar*) (length param*))
              `(let ([,uvar* ,param*] ...) ,x)
              `(lambda (,uvar* ...) ,x))])))
  (define Expr
    (lambda (expr)
      (match expr
        [,x (guard (uvar? x)) x]
        [(if ,[test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        [(quote ,imm) `(quote ,imm)]
        [(let ([,uvar* ,[expr*]] ...) ,[tail])
          `(let ([,uvar* ,expr*] ...) ,tail)]
        [(begin ,[expr*] ... ,[expr])
          `(begin ,expr* ... ,expr)]
        [(letrec ([,uvar* (lambda (,param* ...) ,[tail*])] ...) ,[tail])
          `(letrec ([,uvar* (lambda (,param* ...) ,tail*)] ...) ,tail)]
        [(lambda (,uvar* ...) ,[x])
          `(lambda (,uvar* ...) ,x)]
        [(,prim ,[x*] ...) (guard (assq prim primitives))
          `(,prim ,x* ...)]
        [(,x ,[y*] ...) (guard (lambda-expr? x))
          (convert-lambda x y*)]
        [(,[x] ,[y*] ...) `(,x ,y* ...)])))
  (lambda (x)
    (if *enable-optimize-direct-call*
        (Expr x)
        x)))


;; pass: remove-anonymous-lambda
;; (lambda (formal ...) body) ====>
;;   (letrec ([anon (lambda (formal ...) body)])
;;     anon)
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
          [(,prim ,[(Expr 1) -> x*] ...) (guard (assq prim primitives))
            `(,prim ,x* ...)]
          [(,[(Expr 1) -> x] ,[(Expr 1) -> y*] ...) `(,x ,y* ...)]))))
  (lambda (x)
    ((Expr 0) x)))


;; pass: sanitize-binding-forms
;; (let ([x.4 '0] [f.2 (lambda (x.1) x.1)] [y.3 '1])
;;   (+ x.4 (f.2 y.3)))
;; ====>
;; (letrec ([f.2 (lambda (x.1) x.1)])
;;   (let ([x.4 '0] [y.3 '1])
;;     (+ x.4 (f.2 y.3))))
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
      [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
      [(quote ,im) `(quote ,im)]
      [,x (guard (uvar? x)) x]
      [(begin ,[expr*] ... ,[expr])
        `(begin ,expr* ... ,expr)]
      [(letrec ([,uvar* (lambda (,param* ...) ,[tail*])] ...) ,[tail])
        `(letrec ([,uvar* (lambda (,param* ...) ,tail*)] ...) ,tail)]
      [(,prim ,[x*] ...) (guard (assq prim primitives))
        `(,prim ,x* ...)]
      [(lambda (,uvar* ...) ,[x]) `(lambda (,uvar* ...) ,x)]
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
      [(,[x] ,[y*] ...) `(,x ,y* ...)])))


;; pass: uncover-free 
;; 将自由变量都放入 free 表中
#|output:
Program   ----> Expr
Expr      ----> uvar
            |   (quote Immediate)
            |   (if Expr Expr Expr)
            |   (begin Expr* Expr)
            |   (let ([uvar Expr]*) Expr)
            |   (letrec ([uvar (lambda (uvar*) (free (free-uvar*) Expr))]*) Expr)
            |   (primitive Expr*)
            |   (Expr Expr*)
Immediate ----> fixnum | () | #t | #f
|#
(define-who uncover-free
  (define clean-up
    (lambda (x)
      (cond
        [(null? x) '()]
        [(null? (car x)) (clean-up (cdr x))]
        [(list? (car x)) (set-cons (caar x) (clean-up (cdr x)))]
        [else (set-cons (car x) (clean-up (cdr x)))])))
  (define Expr
    (lambda (x)
      (match x
        ;; Expr      ----> uvar
        [,uvar (guard (uvar? uvar)) (values uvar `(,uvar))]
        ;; Expr      ----> (if Expr Expr Expr)
        [(if ,[t t-f] ,[c c-f] ,[a a-f])
          (values `(if ,t ,c ,a) (union t-f c-f a-f))]
        ;; (lambda (uvar*) Expr)
        ;; ====> (lambda (uvar*) (free free-vars Expr))
        [(lambda (,param* ...) ,[stmt* free])
          (let ([free-vars (difference (clean-up free) param*)])
            (values `(lambda (,param* ...) (free ,free-vars ,stmt*)) free-vars))]
        ;; Expr      ----> (quote Immediate)
        [(quote ,imm) (values `(quote ,imm) '())]
        ;; Expr      ----> (begin Expr* Expr)
        [(begin ,[stmt* free-var**] ... ,[stmt free-var*])
          (values `(begin ,stmt* ... ,stmt) (union (apply append free-var**) free-var*))]
        ;; Expr      ----> (letrec ([uvar (lambda (uvar*) Expr)]*) Expr)
        ;;           ====> (letrec ([uvar (lambda (uvar*) (free free-vars Expr))]*) Expr)
        [(letrec ([,uvar* ,[body* free*]] ...) ,[expr free])
          (values `(letrec ([,uvar* ,body*] ...) ,expr) (difference (union (apply append free*) free) uvar*))]
        ;; Expr      ----> (let ([uvar Expr]*) Expr)
        [(let ([,uvar* ,[expr* free*]] ...) ,[tail free])
          (values `(let ([,uvar* ,expr*] ...) ,tail) (difference (union (apply append free*) free) uvar*))]
        ;; Expr      ----> (primitive Expr*)
        [(,prim ,[expr* free*] ...) (guard (assq prim primitives))
          (values `(,prim ,expr* ...) (apply append free*))]
        ;; Expr      ----> (Expr Expr*)
        [(,[expr free] ,[rem* free*] ...)
          (values `(,expr ,rem* ...) (union (apply append free*) free))])))
  (lambda (x)
    (let-values ([(expr free-vars) (Expr x)])
      (unless (null? free-vars)
        (error who "Bindings not null"))
      expr)))


;; pass: convert-closures
;; 首先将原来给 lambda 函数命名的 uvar 改成 label，然后给每一个参数增加一个函数指针
;; 在函数体中指明函数指针与函数参数，在剩余部分，指明函数变量，将上面的 label 以及自由变量设置上
;; 对函数的调用增加第一个参数为函数指针
#|output:
Program   ----> Expr
Expr      ----> uvar
            |   (quote Immediate)
            |   (if Expr Expr Expr)
            |   (begin Expr* Expr)
            |   (let ([uvar Expr]*) Expr)
            |   (primitive Expr*)
            |   (uvar uvar Expr*)
            |   (letrec ([label (lambda (func-ptr uvar*) (bind-free (func-ptr free-uvar*) Expr))]*)
                        (closures ((func-uvar label free-uvar*)*) Expr))
Immediate ----> fixnum | () | #t | #f
|#
(define-who convert-closures
  (define Expr
    (lambda (x)
      (match x
        ;; Expr      ----> uvar
        [,uvar (guard (uvar? uvar)) uvar]
        ;; Expr      ----> (if Expr Expr Expr)
        [(if ,[test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Expr      ----> (quote Immediate)
        [(quote ,im-expr) `(quote ,im-expr)]
        ;; Expr      ----> (begin Expr* Expr)
        [(begin ,[expr*] ... ,[tail])
          `(begin ,expr* ... ,tail)]
        ;; Expr      ----> (letrec ([uvar (lambda (uvar*) (free (free-uvar*) Expr))]*) Expr)
        ;;           ====> (letrec ([label (lambda (func-ptr uvar*) (bind-free (func-ptr free-uvar*) Expr))]*)
        ;;                         (closures ((func-uvar label free-uvar*)*) Expr))
        [(letrec ([,uvar* ,body*] ...) ,[tail])
          (let* ([label* (map unique-label uvar*)]
                 [new-body* (map Body body*)]
                 [local-closure* (map Closure uvar* label* body*)])
            `(letrec ([,label* ,new-body*] ...) (closures ,local-closure* ,tail)))]
        ;; Expr      ----> (let ([uvar Expr]*) Expr)
        [(let ([,uvar* ,[expr*]] ...) ,[tail])
          `(let ([,uvar* ,expr*] ...) ,tail)]
        ;; Expr      ----> (primitive Expr*)
        [(,prim ,[expr*] ...) (guard (assq prim primitives))
          `(,prim ,expr* ...)]
        ;; Expr      ----> (Expr Expr*)
        ;;           ====> (uvar uvar Expr*)
        [(,[expr] ,[rem*] ...)
          (if (uvar? expr)
              `(,expr ,expr ,rem* ...)
              (let ([local (unique-name 't)])
                `(let ([,local ,expr])
                   (,local ,local ,rem* ...))))])))
  (define Body
    (lambda (body)
      (match body
        ;; (lambda (uvar*) (free (free-uvar*) Expr))
        ;; =====> (lambda (func-ptr uvar*) (bind-free (func-ptr free-uvar*) Expr))
        [(lambda (,param* ...) (free (,free* ...) ,[Expr -> body]))
          (let ([func-ptr (unique-name 'fp)])
            `(lambda (,func-ptr ,param* ...) (bind-free (,func-ptr ,free* ...) ,body)))])))
  (define Closure
    (lambda (func-var label body)
      (match body
        ;; (lambda (uvar*) (free (free-uvar*) Expr))
        [(lambda ,param* (free (,free* ...) ,other))
          `(,func-var ,label ,free* ...)])))
  (lambda (x)
    (Expr x)))


;; pass: optimize-known-call
(define-who optimize-known-call
  (define collect-closures
    (lambda (expr)
      (match expr
        [,uvar (guard (uvar? uvar)) '()]
        [(if ,[t] ,[c] ,[a])
          `(,t ... ,c ... ,a ...)]
        [(quote ,x) '()]
        [(begin ,[expr*] ... ,[tail])
          `(,expr* ... ... ,tail ...)]
        [(letrec ([,label* (lambda (,param* ...) (bind-free (,fptr ,free* ...) ,[body*]))] ...)
           (closures (,func* ...) ,[tail]))
          `(,body* ... ... ,(map car func*) ,tail ...)]
        [(let ([,uvar* ,[expr*]] ...) ,[tail])
          `(,expr* ... ... ,tail ...)]
        [(,prim ,[expr*] ...) (guard (assq prim primitives))
          `(,expr* ... ...)]
        [(,[expr-a] ,[expr] ,[rem*] ...)
          `(,expr-a ... ,expr ... ,rem* ... ...)])))
  (define Expr
    (lambda (func*)
      (lambda (expr)
        (match expr
          [,uvar (guard (uvar? uvar)) uvar]
          [(if ,[t] ,[c] ,[a])
            `(if ,t ,c ,a)]
          [(quote ,imm) `(quote ,imm)]
          [(begin ,[expr*] ... ,[tail])
            `(begin ,expr* ... ,tail)]
          [(letrec ([,label* (lambda (,param* ...) (bind-free (,fptr ,free* ...) ,[body]))] ...)
             (closures (,clos* ...) ,[tail]))
            `(letrec ([,label* (lambda (,param* ...) (bind-free (,fptr ,free* ...) ,body))] ...)
              (closures (,clos* ...) ,tail))]
          [(let ([,uvar* ,[expr*]] ...) ,[tail])
            `(let ([,uvar* ,expr*] ...) ,tail)]
          [(,prim ,[expr*] ...) (guard (assq prim primitives))
            `(,prim ,expr* ...)]
          [(,[expr-a] ,[expr] ,[rem*] ...)
            (if (memq expr-a func*)
                `(,(unique-label expr-a) ,expr ,rem* ...)
                `(,expr-a ,expr ,rem* ...))]))))
  (lambda (x)
    (if *enable-optimize-known-call*
        (let ([closures (apply append (remq '() (collect-closures x)))])
          ((Expr closures) x))
        x)))


;; pass: introduce-procedure-primitives
;; 在 letrec 身体开始前，首先用 (let ([func-uvar (make-procedure func-label free-length)])) 将函数绑定到变量，
;; 其中 func-label 是函数的 label，free-length 是内部自由变量的数目。然后 (procedure-set! func-uvar free-index free-uvar)
;; 将 func-uvar 这个函数对象的每一个自由变量绑定变量 free-uvar，在使用自由变量的位置使用 (procedure-ref func-ptr pos)
;; 定义函数时增加第一个参数为 func-ptr 在调用时需要添加这个参数，而添加的参数为 uvar 而该 uvar 指代的是 procedure 对象。
;; 所以 func-ptr 其实会被赋值为 procedure 对象。在调用时函数时，如果使用的函数名不在自由变量中，使用 (procedure-code uvar)
;; 来获取函数对象，procedure-code 本质上是获取 label
#|output:
Program   ----> Expr
Expr      ----> uvar
            |   (quote Immediate)
            |   (if Expr Expr Expr)
            |   (begin Expr* Expr)
            |   (let ([uvar Expr]*) Expr)
            |   (primitive Expr*)
            |   (procedure-code uvar)
            |   (procedure-ref func-ptr pos)
            |   (Expr Expr*)
            |   (make-procedure label free-len)
            |   (procedure-set! func-uvar free-index Expr)
            |   (letrec ([label Body]*) Expr)
Immediate ----> fixnum | () | #t | #f
Body      ----> (lambda (func-ptr uvar*) Expr)
|#
(define-who introduce-procedure-primitives
  (define find-pos
    (lambda (pos needle haystack)
      (cond
        [(null? haystack) '-1]
        [(eq? needle (car haystack)) pos]
        [else (find-pos (add1 pos) needle (cdr haystack))])))
  (define make-list
    (lambda (start val)
      (cond
        [(> start val) '()]
        [else (cons start (make-list (add1 start) val))])))
  (define make-procs-set!
    (lambda (closure)
      ;; (func-uvar label free-uvar*)
      (lambda (fptr free-list)
        (let* ([func-uvar (list-ref closure 0)]
               [arg* (cddr closure)]
               [arg-length (length arg*)]
               ;; (0, 1, ... length-1)
               [index-list (make-list '0 (sub1 arg-length))])
          (map (lambda (x y)
                 (let ([pos (find-pos '0 x free-list)])
                   (if (eq? pos '-1)
                       `(procedure-set! ,func-uvar (quote ,y) ,x)
                       `(procedure-set! ,func-uvar (quote ,y) (procedure-ref ,fptr (quote ,pos))))))
            arg* index-list)))))
  (define make-funcs
    (lambda (x)
      ;; (func-uvar label free-uvar*)
      ;; ====> (uvar (make-procedure label free-len))
      (let ([func-uvar (list-ref x 0)]
            [func-label (list-ref x 1)]
            [arg-length (length (cddr x))])
        `(,func-uvar (make-procedure ,func-label (quote ,arg-length))))))
  (define Tail
    (lambda (fptr free-list)
      (lambda (tail)
        (match tail
          ;; (closures ((func-uvar label free-uvar*)*) Expr)
          ;; ====> (let ([func-uvar (make-procedure label free-len)]*)
          ;;         (begin (procedure-set! func-uvar free-index free-uvar)*
          ;;              | (procedure-set! func-uvar free-index (procedure-ref func-ptr pos))*
          ;;           Expr))
          [(closures (,funcs* ...) ,[(Expr fptr free-list) -> new-tail])
            (let ([functions (map make-funcs funcs*)]
                  [proc-set (map (lambda (fn)
                                   (fn fptr free-list))
                              (map make-procs-set! funcs*))])
              `(let ,functions ,(make-begin `(,proc-set ... ... ,new-tail))))]))))
  (define Expr
    (lambda (fptr free-list)
      (lambda (expr)
        (match expr
          ;; Expr      ----> (if Expr Expr Expr)
          [(if ,[test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Expr      ----> (quote Immediate)
          [(quote ,imm) `(quote ,imm)]
          ;; Expr      ----> (begin Expr* Expr)
          [(begin ,[expr*] ... ,[tail])
            `(begin ,expr* ... ,tail)]
          ;; Expr      ----> (let ([uvar Expr]*) Expr)
          [(let ([,uvar* ,[expr*]] ...) ,[tail])
            `(let ([,uvar* ,expr*] ...) ,tail)]
          ;; (lambda (func-ptr uvar*) (bind-free (func-ptr free-uvar*) Expr))
          ;; ====> (lambda (func-ptr uvar*) Expr)
          [(lambda (,param* ...) (bind-free (,fptr ,free* ...) ,[(Expr fptr free*) -> body]))
            `(lambda ,param* ,body)]
          ;; Expr      ----> (letrec ([label (lambda (func-ptr uvar*) (bind-free (func-ptr uvar*) Expr))]*)
          ;;                         (closures ((uvar label uvar*)*) Expr))
          ;;           ====> (letrec ([label (lambda (func-ptr uvar*) Expr)])
          ;;                   (let ([uvar (make-procedure label free-len)]*)
          ;;                     (begin (procedure-set! func-uvar free-index free-uvar)*
          ;;                          | (procedure-set! func-uvar free-index (procedure-ref func-ptr pos))*
          ;;                     Expr)))
          [(letrec ([,label* ,[body*]] ...) ,[(Tail fptr free-list) -> tail])
            `(letrec ([,label* ,body*] ...) ,tail)]
          ;; Expr      ----> (primitive Expr*)
          [(,prim ,[expr*] ...) (guard (assq prim primitives))
            `(,prim ,expr* ...)]
          ;; Expr      ----> uvar
          ;;           ====> uvar
          ;;               | (procedure-ref func-ptr pos)
          [,uvar (guard (uvar? uvar))
            (if (null? free-list)
                uvar
                (let ([pos (find-pos 0 uvar free-list)])
                  (if (eq? pos -1)
                      uvar
                      `(procedure-ref ,fptr (quote ,pos)))))]
          ;; Expr      ----> (uvar uvar Expr*)
          ;;           ====> ((procedure-ref func-ptr pos) Expr*)
          [(,expr-a ,[expr] ,[rem*] ...) (guard (label? expr-a))
            (if (null? free-list)
                `(,expr-a ,expr ,rem* ...)
                (let ([pos (find-pos 0 expr free-list)])
                  (if (eq? pos -1)
                      `(,expr-a ,expr ,rem* ...)
                      `((procedure-ref ,fptr (quote ,pos))
                        ,rem* ...))))]
          ;; Expr      ----> (uvar uvar Expr*)
          ;;           ====> ((procedure-code uvar) uvar Expr*)
          ;;               | ((procedure-ref func-ptr pos) Expr*)
          [(,[expr-a] ,[expr] ,[rem*] ...)
            (if (null? free-list)
                `((procedure-code ,expr-a) ,expr ,rem* ...)
                (let ([pos (find-pos 0 expr free-list)])
                  (if (eq? pos -1)
                      `((procedure-code ,expr-a) ,expr ,rem* ...)
                      `((procedure-ref ,fptr (quote ,pos))
                        ,rem* ...))))]))))
  (lambda (x)
    ((Expr '() '()) x)))


;; pass: lift-letrec
;; This pass simply moves all letrec bindings from where they appear into a letrec expression wrapped
;; around the outermost expression, removing all of the internal letrec expressions in the process.
(define-who lift-letrec
  (define definitions '())
  (define Expr
    (lambda (x)
      (match x
        ;; Expr      ----> label
        [,label (guard (label? label)) label]
        ;; Expr      ----> uvar
        [,uvar (guard (uvar? uvar)) uvar]
        ;; Expr      ----> (quote Immediate)
        [(quote ,[imm]) `(quote ,imm)]
        ;; Expr      ----> (if Expr Expr Expr)
        [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
        ;; Expr      ----> (begin Expr* Expr)
        [(begin ,[e*] ...) `(begin ,e* ...)]
        ;; Expr      ----> (let ([uvar Expr]*) Expr)
        [(let ([,uvar* ,[expr*]] ...) ,[tail]) `(let ([,uvar* ,expr*] ...) ,tail)]
        ;; Expr      ----> (letrec ([label (lambda (uvar*) Expr)]*) Expr)
        [(letrec ([,label* (lambda (,fml** ...) ,[body*])] ...) ,[tail])
          (set! definitions (append definitions `([,label* (lambda (,fml** ...) ,body*)] ...)))
          tail]
        ;; Expr      ----> (prim Expr*)
        ;;             |   (Expr Expr*)
        [(,[f] ,[x*] ...) `(,f ,x* ...)]
        ;; Immediate ----> fixnum | () | #t | #f
        [,x x])))
  (lambda (x)
    (set! definitions '())
    ;; Program   ----> Expr
    (let ([tail (Expr x)]) `(letrec ,definitions ,tail))))


;; pass: normalize-context
#| output:
Program   ----> (letrec ([label (lambda (uvar*) Value)]*) Value)
Value     ----> label
            |   uvar
            |   (quote Immediate)
            |   (if Pred Value Value)
            |   (begin Effect* Value)
            |   (let ([uvar Value]*) Value)
            |   (value-prim Value*)
            |   (Value Value*)
Pred      ----> (true)
            |   (false)
            |   (if Pred Pred Pred)
            |   (begin Effect* Pred)
            |   (let ([uvar Value]*) Pred)
            |   (pred-prim Value*)
Effect    ----> (nop)
            |   (if Pred Effect Effect)
            |   (begin Effect* Effect)
            |   (let ([uvar Value]*) Effect)
            |   (effect-prim Value*)
            |   (Value Value*)
Immediate ----> fixnum | () | #t | #f
|#
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
        [(void) '(nop)]
        [,x (guard (uvar? x)) '(nop)]
        [(if ,[Pred -> t] ,[c] ,[a]) `(if ,t ,c ,a)]
        [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
        [(let ([,uvar* ,[Value -> value*]] ...) ,[tail])
          `(let ([,uvar* ,value*] ...) ,tail)]
        [(,prim ,[Value -> val*] ...) (guard (assq prim effect-prims))
          `(,prim ,val* ...)]
        [(,prim ,val* ...) (guard (or (assq prim value-prims) (assq prim pred-prims)))
          `(nop)]
        [(,[Value -> val] ,[Value -> val*] ...) `(,val ,val* ...)])))
  (define Pred
    (lambda (x)
      (match x
        ;; Expr      ----> label
        ;;           ====> (true)
        [,x (guard (label? x)) '(true)]
        ;; Expr      ----> uvar
        ;;           ====> (if Pred Pred Pred)
        [,x (guard (uvar? x)) `(if (eq? ,x '#f) (false) (true))]
        ;; Expr      ----> (quote Immediate)
        ;;           ====> (if Pred Pred Pred)
        [(quote ,imm) `(if (eq? (quote ,imm) '#f) (false) (true))]
        ;; Expr      ----> (if Expr Expr Expr)
        ;;           ====> (if Pred Pred Pred)
        [(if ,[t] ,[c] ,[a]) `(if ,t ,c ,a)]
        ;; Expr      ----> (begin Expr* Expr)
        ;;           ====> (begin Effect* Pred)
        [(begin ,[Effect -> ef*] ... ,[ef]) (make-nopless-begin `(,ef* ... ,ef))]
        ;; Expr      ----> (let ([uvar Expr]*) Expr)
        ;;           ====> (let ([uvar Value]*) Pred)
        [(let ([,uvar* ,[Value -> val*]] ...) ,[tail]) `(let ([,uvar* ,val*] ...) ,tail)]
        ;; Expr      ----> (prim Expr*)
        ;;           ====> (if Pred Pred Pred)
        [(,prim ,[Value -> val*] ...) (guard (assq prim value-prims))
          `(if (eq? (,prim ,val* ...) '#f) (false) (true))]
        ;; Expr      ----> (prim Expr*)
        [(,prim ,[Value -> val*] ...) (guard (assq prim pred-prims))
          `(,prim ,val* ...)]
        ;; Expr      ----> (prim Expr*)
        ;;           ====> (begin Effect* Pred)
        [(,prim ,[Value -> val*] ...) (guard (assq prim effect-prims))
          (make-nopless-begin `((,prim ,val* ...) (true)))]
        ;; Expr      ----> (Expr Expr*)
        ;;           ====> (if Pred Pred Pred)
        [(,[Value -> x] ,[Value -> x*] ...) `(if (eq? (,x ,x* ...) '#f) (false) (true))])))
  (define Value
    (lambda (x)
      (match x
        ;; Expr      ----> label
        ;;             |   uvar
        [,x (guard (or (label? x) (uvar? x))) x]
        ;; Expr      ----> (quote Immediate)
        [(quote ,imm) `(quote ,imm)]
        ;; Expr      ----> (if Expr Expr Expr)
        ;;           ====> (if Pred Value Value)
        [(if ,[Pred -> t] ,[c] ,[a]) `(if ,t ,c ,a)]
        ;; Expr      ----> (begin Expr* Expr)
        ;;           ====> (begin Effect* Value)
        [(begin ,[Effect -> ef*] ... ,[ef]) (make-nopless-begin `(,ef* ... ,ef))]
        ;; Expr      ----> (let ([uvar Expr]*) Expr)
        ;;           ====> (let ([uvar Value]*) Value)
        [(let ([,uvar* ,[val*]] ...) ,[tail]) `(let ([,uvar* ,val*] ...) ,tail)]
        ;; Expr      ----> (prim Expr*)
        ;;           ====> (value-prim Value*)
        [(,prim ,[val*] ...) (guard (assq prim value-prims))
          `(,prim ,val* ...)]
        ;; Expr      ----> (prim Expr*)
        ;;           ====> (if Pred Value Value)
        [(,prim ,[val*] ...) (guard (assq prim pred-prims))
          `(if (,prim ,val* ...) '#t '#f)]
        ;; Expr      ----> (prim Expr*)
        ;;           ====> (begin Effect* Value)
        [(,prim ,[val*] ...) (guard (assq prim effect-prims))
          (make-nopless-begin `((,prim ,val* ...) (void)))]
        ;; Expr      ----> (Expr Expr*)
        ;;           ====> (Value Value*)
        [(,[val] ,[val*] ...) `(,val ,val* ...)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda (,fml** ...) ,[Value -> val*])] ...) ,[Value -> tail])
        `(letrec ([,label* (lambda (,fml** ...) ,val*)] ...) ,tail)])))


;; pass: optimize-jumps
;; input:
#|
Program ----> (letrec ([label (lambda () Tail)]*) Tail)
Tail    ----> (Triv)
          |   (if (relop Triv Triv) (,label) (,label))
          |   (begin Effect* Tail)
Effect  ----> (set! Loc Triv)
          |   (set! Loc (binop Triv Triv))
Loc     ----> reg | fvar
Triv    ----> Loc | int | label
|#
(define optimize-jumps
  (lambda (x)
    (define assoc-list '())
    (define build-assoc-list
      (lambda (label* tail* res)
        (for-each
          (lambda (label tail)
            (match tail
              [(,last) (guard (label? last))
                (let ([symbol (walk last '#f)])
                  (cond
                    [(eq? symbol '#f) (set! assoc-list (cons (cons label last) assoc-list))]
                    [(eq? symbol label) (set! res (cons `(,label (lambda () ,tail)) res))]
                    [else (set! assoc-list (cons (cons label symbol) assoc-list))]))]
              [,other (set! res (cons `(,label (lambda () ,tail)) res))]))
          label* tail*) res))
    (define walk
      (lambda (val sym)
        (cond
          [(null? assoc-list) sym]
          [(assq val assoc-list) => (lambda (x) (walk (cdr x) (cdr x)))]
          [else sym])))
    (define Prog
      (lambda (x)
        (match x
          [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
            `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)])))
    (define Tail
      (lambda (x)
        (match x
          [(if (,relop ,[Triv -> a] ,[Triv -> b]) (,[Triv -> cl]) (,[Triv -> al]))
            `(if (,relop ,a ,b) (,cl) (,al))]
          [(begin ,[Effect -> ef*] ... ,[tail]) `(begin ,ef* ... ,tail)]
          [(,[Triv -> triv]) `(,triv)])))
    (define Effect
      (lambda (x)
        (match x
          [(set! ,x ,[Triv -> y]) `(set! ,x ,y)]
          [(set! ,x (,binop ,[Triv -> y] ,[Triv -> z])) `(set! ,x (,binop ,y ,z))])))
    (define Triv
      (lambda (x)
        (cond
          [(label? x) (walk x x)]
          [else x])))
    (if *enable-optimize-jumps*
        (match x
          [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
            (Prog `(letrec ,(build-assoc-list label* tail* '()) ,tail))])
        x)))


;; pass: specify-representation
;; The goal of this pass is to convert all Scheme datatypes to their ptr equivalents 
;; so they are represented asintegers in the output language, and at the same time, 
;; translate calls to Scheme primitives into calls to UIL primitives.
(define-who specify-representation
  (define handle-pred-op
    (lambda (rator rand*)
      (cond 
			  [(memq rator '(> < = <= >= )) `(,rator ,@rand*)]
        [(eq? rator 'eq?) `(= ,@rand*)]
        [(eq? rator 'boolean?)
          `(= (logand ,(car rand*) ,mask-boolean) ,tag-boolean)]
        [(eq? rator 'vector?)
          `(= (logand ,(car rand*) ,mask-vector) ,tag-vector)]
        [(eq? rator 'fixnum?)
          `(= (logand ,(car rand*) ,mask-fixnum) ,tag-fixnum)]
        [(eq? rator 'null?)
          `(= ,(car rand*) ,(Immediate '()))]
        [(eq? rator 'pair?)
          `(= (logand ,(car rand*) ,mask-pair) ,tag-pair)]
        [(eq? rator 'procedure?)
          `(= (logand ,(car rand*) ,mask-procedure) ,tag-procedure)])))
  (define handle-effect-op
    (lambda (rator rand*)
      (cond
        [(eq? rator 'set-car!) `(mset! ,(car rand*) ,(- disp-car tag-pair) ,(cadr rand*))]
        [(eq? rator 'set-cdr!) `(mset! ,(car rand*) ,(- disp-cdr tag-pair) ,(cadr rand*))]
        [(eq? rator 'vector-set!)
          (let ([value (cadr rand*)])
            (if (integer? value)
                `(mset! ,(car rand*) ,(+ (- disp-vector-data tag-vector) value) ,(caddr rand*))
                `(mset! ,(car rand*) (+ ,(- disp-vector-data tag-vector) ,value) ,(caddr rand*))))]
        [(eq? rator 'procedure-set!)
          (let ([value (cadr rand*)])
            (if (integer? value)
                `(mset! ,(car rand*) ,(+ (- disp-procedure-data tag-procedure) value) ,(caddr rand*))
                `(mset! ,(car rand*) (+ ,(- disp-procedure-data tag-procedure) ,value) ,(caddr rand*))))])))
  (define handle-value-op
    (lambda (rator rand*)
      (cond
        [(eq? rator 'cons)
          (let ([x (unique-name 't)]
                [y (unique-name 't)]
                [z (unique-name 't)])
            `(let ([,x ,(car rand*)]
                   [,y ,(cadr rand*)]
                   [,z (+ (alloc ,size-pair) ,tag-pair)])
              (begin
                (mset! ,z ,(- disp-car tag-pair) ,x)
                (mset! ,z ,(- disp-cdr tag-pair) ,y)
                ,z)))]
        [(eq? rator 'car)
          `(mref ,(car rand*) ,(- disp-car tag-pair))]
        [(eq? rator 'cdr)
          `(mref ,(car rand*) ,(- disp-cdr tag-pair))]
        [(eq? rator 'make-vector)
          (let ([vector (unique-name 't)]
                [size (car rand*)])
            (if (integer? size)
                `(let ([,vector (+ (alloc ,(+ disp-vector-data size)) ,tag-vector)])
                  (begin
                    (mset! ,vector ,(- disp-vector-length tag-vector) ,size)
                    ,vector))
                `(let ([,vector (+ (alloc (+ ,disp-vector-data ,size)) ,tag-vector)])
                  (begin
                    (mset! ,vector ,(- disp-vector-length tag-vector) ,size)
                    ,vector))))]
        [(eq? rator 'vector-length)
          `(mref ,(car rand*) ,(- disp-vector-length tag-vector))]
        [(eq? rator 'vector-ref)
          (let ([value (cadr rand*)])
            (if (integer? value)
                `(mref ,(car rand*) ,(+ (- disp-vector-data tag-vector) value))
                `(mref ,(car rand*) (+ ,(- disp-vector-data tag-vector) ,value))))]
        [(or (eq? rator '+)
             (eq? rator '-))
          `(,rator ,@rand*)]
        [(eq? rator 'void) $void]
        ;; TODO: size 没有实际用到？
        [(eq? rator 'make-procedure)
          (let ([size-var (unique-name 't)]
                [size (cadr rand*)]
                [func (car rand*)])
            (if (integer? size)
                `(let ([,size-var (+ (alloc ,(+ disp-procedure-data size)) ,tag-procedure)])
                   (begin
                     (mset! ,size-var ,(- disp-procedure-code tag-procedure) ,func)
                     ,size-var))
                `(let ([,size-var (+ (alloc (+ ,disp-procedure-code ,size)) ,tag-procedure)])
                   (begin
                     (mset! ,size-var ,(- disp-procedure-code tag-procedure) ,func)
                     ,size-var))))]
        [(eq? rator 'procedure-code)
          `(mref ,(car rand*) ,(- disp-procedure-code tag-procedure))]
        [(eq? rator 'procedure-ref)
          (let ([value (cadr rand*)])
            (if (integer? value)
                `(mref ,(car rand*) ,(+ (- disp-procedure-data tag-procedure) value))
                `(mref ,(car rand*) (+ ,(- disp-procedure-data tag-procedure) ,value))))])))

  (define Value
    (lambda (x)
      (match x
        ;; Value     ----> label
        ;;             |   uvar
        [,x (guard (or (label? x) (uvar? x))) x]
        ;; Value     ----> (quote Immediate)
        ;;           ====> Immediate
        [(quote ,[Immediate -> imm]) imm]
        ;; Value     ----> (if Pred Value Value)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Value     ----> (begin Effect* Value)
        [(begin ,[Effect -> ef*] ... ,[val])
          `(begin ,ef* ... ,val)]
        ;; Value     ----> (let ([uvar Value]*) Value)
        [(let ([,uvar* ,[value*]] ...) ,[value])
          `(let ([,uvar* ,value*] ...) ,value)]
        [(* ,[a] ,[b])
          (cond
            [(integer? a) `(* ,(sra a shift-fixnum) ,b)]
            [(integer? b) `(* ,a ,(sra b shift-fixnum))]
            [else `(* ,a (sra ,b ,shift-fixnum))])]
        ;; Value     ----> (value-prim Value*)
        [(,prim ,[val*] ...) (guard (assq prim value-prims))
          (handle-value-op prim val*)]
        ;; Value     ----> (Value Value*)
        [(,[val] ,[val*] ...) `(,val ,val* ...)])))
  (define Pred
    (lambda (x)
      (match x
        ;; Pred      ----> (true)
        [(true) '(true)]
        ;; Pred      ----> (false)
        [(false) '(false)]
        ;; Pred      ----> (if Pred Pred Pred)
        [(if ,[test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Pred      ----> (begin Effect* Pred)
        [(begin ,[Effect -> ef*] ... ,[ef])
          `(begin ,ef* ... ,ef)]
        ;; Pred      ----> (let ([uvar Value]*) Pred)
        [(let ([,uvar* ,[Value -> value*]] ...) ,[pr])
          `(let ([,uvar* ,value*] ...) ,pr)]
        ;; Pred      ----> (pred-prim Value*)
        [(,prim ,[Value -> val*] ...) (guard (assq prim pred-prims))
          (handle-pred-op prim val*)])))
  (define Effect
    (lambda (x)
      (match x
        ;; Effect    ----> (nop)
        [(nop) '(nop)]
        ;; Effect    ----> (if Pred Effect Effect)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Effect    ----> (begin Effect* Effect)
        [(begin ,[ef*] ... ,[ef])
          `(begin ,ef* ... ,ef)]
        ;; Effect    ----> (let ([uvar Value]*) Effect)
        [(let ([,uvar* ,[Value -> value*]] ...) ,[ef])
          `(let ([,uvar* ,value*] ...) ,ef)]
        ;; Effect    ----> (effect-prim Value*)
        [(,prim ,[Value -> val*] ...) (guard (assq prim effect-prims))
          (handle-effect-op prim val*)]
        ;; Effect    ----> (Value Value*)
        [(,[Value -> val] ,[Value -> val*] ...)
          `(,val ,val* ...)])))
  (define Immediate
    (lambda (x)
      ;; Immediate ----> fixnum | () | #t | #f
      (match x
        [#t $true]
        [#f $false]
        [() $nil]
        [,t (guard (integer? t))
          (ash t shift-fixnum)])))
  (lambda (x)
    (match x
      ;; Program   ----> (letrec ([label (lambda (uvar*) Value)]*) Value)
      [(letrec ([,label* (lambda (,uvar** ...) ,[Value -> val*])] ...) ,[Value -> val])
        `(letrec ([,label* (lambda (,uvar** ...) ,val*)] ...) ,val)])))


;; pass: uncover-locals
;; The only change to the grammar is the introduction of the locals form.
;; Program ----> (letrec ([label (lambda (uvar*) Tail)]*) Tail)
;; Body ----> (locals (uvar*) Tail)
(define-who uncover-locals
  (define Value
    (lambda (x)
      (match x
        ;; Value   ----> (alloc Value)
        [(alloc ,[val]) val]
        ;; Value   ----> (binop Value Value)
        [(,binop ,[x] ,[y])
          (guard (memq binop '(+ - * logand logor mref)))
          (union x y)]
        ;; Value   ----> (if Pred Value Value)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          (union test conseq alt)]
        ;; Value   ----> (begin Effect* Value)
        [(begin ,[Effect -> ef*] ... ,[ef])
          `(,ef* ... ... ,ef ...)]
        ;; Value   ----> (let ([uvar Value]*) Value)
        [(let ([,new-uvar* ,[uvar*]] ...) ,[val])
          `(,new-uvar* ... ,uvar* ... ... ,val ...)]
        ;; Value   ----> (Value Value*)
        [(,[rator] ,[rand*] ...)
          `(,rator ... ,rand* ... ...)]
        ;; Value   ----> Triv
        [,triv '()])))
  (define Effect
    (lambda (x)
      (match x
        ;; Effect  ----> (nop)
        [(nop) '()]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          (union test conseq alt)]
        ;; Effect  ----> (let ([uvar Value]*) Effect)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[ef])
          `(,new-uvar* ... ,uvar* ... ... ,ef ...)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[ef*] ... ,[ef])
          `(,ef* ... ... ,ef ...)]
        ;; Effect  ----> (mset! Value Value Value)
        [(mset! ,[Value -> base] ,[Value -> offset] ,[Value -> value])
          (union base offset value)]
        ;; Effect  ----> (Value Value*)
        [(,[Value -> rator] ,[Value -> rand*] ...)
          `(,rator ... ,rand* ... ...)])))
  (define Pred
    (lambda (x)
      (match x
        ;; Pred    ----> (let ([uvar Value]*) Pred)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[pr])
          `(,new-uvar* ... ,uvar* ... ... ,pr ...)]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> ef*] ... ,[pr])
          `(,ef* ... ... ,pr ...)]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[test] ,[conseq] ,[alt])
          (union test conseq alt)]
        ;; Pred    ----> (relop Value Value)
        [(,relop ,[Value -> x] ,[Value -> y])
          (guard (memq relop '(< <= = >= >)))
          (union x y)]
        ;; Pred    ----> (true)
        ;;           |   (false)
        [,other '()])))
  (define Tail
    (lambda (x)
      (match x 
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          (union test conseq alt)]
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,[Effect -> ef*] ... ,[tail])
          `(,ef* ... ... ,tail ...)]
        ;; Tail    ----> (let ([uvar Value]*) Tail)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[tail])
          `(,new-uvar* ... ,uvar* ... ... ,tail ...)]
        ;; Tail    ----> (alloc Value)
        [(alloc ,[Value -> val]) val]
        ;; Tail    ----> (binop Value Value)
        [(binop ,[Value -> x] ,[Value -> y])
          (guard (memq binop '(+ - * logand logor sra mref)))
          (union x y)]
        ;; Tail    ----> (Value Value*)
        [(,[Value -> rator] ,[Value -> rand*] ...)
          `(,rator ... ,rand* ... ...)]
        ;; Tail    ----> Triv
        [,triv '()])))
  (define Body
    (lambda (x)
      (let ([uvar* (Tail x)])
        `(locals ,uvar* ,x))))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda (uvar*) Tail)]*) Tail)
      [(letrec ([,label* (lambda (,uvar** ...) ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda (,uvar** ...) ,bd*)] ...) ,bd)])))


;; pass: remove-let
;; (let ([x e] ...) body) ----> (begin (set! x e) ... new-body)
(define-who remove-let
  (define Value
    (lambda (x)
      (match x
        ;; Value   ----> (alloc Value)
        [(alloc ,[val]) `(alloc ,val)]
        ;; Value   ----> (binop Value Value)
        [(,binop ,[x] ,[y])
          (guard (memq binop '(+ - * logand logor mref)))
          `(,binop ,x ,y)]
        ;; Value   ----> (if Pred Value Value)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Value   ----> (begin Effect* Value)
        [(begin ,[Effect -> ef*] ... ,[ef])
          (make-begin `(,ef* ... ,ef))]
        ;; Value   ----> (let ([uvar Value]*) Value)
        ;;         ====> (begin (set! uvar Value) ... Value)
        [(let ([,new-uvar* ,[uvar*]] ...) ,[val])
          (make-begin `((set! ,new-uvar* ,uvar*) ... ,val))]
        ;; Value   ----> (Value Value*)
        [(,[rator] ,[rand*] ...)
          `(,rator ,rand* ...)]
        ;; Value   ----> Triv
        [,triv triv])))
  (define Effect
    (lambda (x)
      (match x
        ;; Effect  ----> (nop)
        [(nop) '(nop)]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Effect  ----> (let ([uvar Value]*) Effect)
        ;;         ====> (begin (set! uvar Value) ... Effect)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[ef])
          (make-begin `((set! ,new-uvar* ,uvar*) ... ,ef))]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[ef*] ... ,[ef])
          (make-begin `(,ef* ... ,ef))]
        ;; Effect  ----> (mset! Value Value Value)
        [(mset! ,[Value -> base] ,[Value -> offset] ,[Value -> value])
          `(mset! ,base ,offset ,value)]
        ;; Effect  ----> (Value Value*)
        [(,[Value -> rator] ,[Value -> rand*] ...)
          `(,rator ,rand* ...)])))
  (define Pred
    (lambda (x)
      (match x
        ;; Pred    ----> (let ([uvar Value]*) Pred)
        ;;         ====> (begin (set! uvar Value) ... Pred)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[pr])
          (make-begin `((set! ,new-uvar* ,uvar*) ... ,pr))]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> ef*] ... ,[pr])
          (make-begin `(,ef* ... ,pr))]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Pred    ----> (relop Value Value)
        [(,relop ,[Value -> x] ,[Value -> y])
          (guard (memq relop '(< <= = >= >)))
          `(,relop ,x ,y)]
        ;; Pred    ----> (true)
        ;;           |   (false)
        [,other other])))
  (define Tail
    (lambda (x)
      (match x
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,[Effect -> ef*] ... ,[tail])
          (make-begin `(,ef* ... ,tail))]
        ;; Tail    ----> (let ([uvar Value]*) Tail)
        ;;         ====> (begin (set! uvar Value) ... Tail)
        [(let ([,new-uvar* ,[Value -> uvar*]] ...) ,[tail])
          (make-begin `((set! ,new-uvar* ,uvar*) ... ,tail))]
        ;; Tail    ----> (alloc Value)
        [(alloc ,[Value -> val]) `(alloc ,val)]
        ;; Tail    ----> (binop Value Value)
        [(binop ,[Value -> x] ,[Value -> y])
          (guard (memq binop '(+ - * logand logor sra mref)))
          `(binop ,x ,y)]
        ;; Tail    ----> (Value Value*)
        [(,[Value -> rator] ,[Value -> rand*] ...)
          `(,rator ,rand* ...)]
        ;; Tail    ----> Triv
        [,triv triv])))
  (define Body
    (lambda (x)
      (match x
        ;; Body ----> (locals (uvar*) Tail)
        [(locals (,uvar* ...) ,[Tail -> tail])
          `(locals (,uvar* ...) ,tail)])))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
      [(letrec ([,label* (lambda (,uvar** ...) ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda (,uvar** ...) ,bd*)] ...) ,bd)])))

#|
Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
Body    ----> (locals (uvar*) Tail)
Tail    ----> Triv
          |   (alloc Value)
          |   (mref Value Value)
          |   (binop Value Value)
          |   (Value Value*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Value Value)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! uvar Value)
          |   (mset! Value Value Value) 
          |   (Value Value*)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Value   ----> Triv
          |   (alloc Value)
          |   (mref Value Value)
          |   (binop Value Value)
          |   (Value Value*)
          |   (if Pred Value Value)
          |   (begin Effect* Value)
Triv    ----> uvar | int | label
|#
;; Where uvar is symbol.n where (n >= 0)
;;       binop is +, -, *, logand, logpr, or sra
;;       relop is <, <=, =, >=, or >
;;       reg is rax, rcx, rdx, rbx, rbp, rdi, rsi, r8,
;;              r9, r10, r11, r12, r13, r14, or r15
;;       label is symbol$n where (n >= 0)
;;       fvar is fvn where (n >= 0)


;; pass: verify-uil
;; to verify that program conforms to the subset of scheme grammar
(define-who verify-uil
  (define verify-x-list
    (lambda (x* x? what)
      (let loop ([x* x*] [idx* '()])
        (unless (null? x*)
          (let ([x (car x*)] [x* (cdr x*)])
            (unless (x? x)
              (errorf who "invalid ~s ~s found" what x))
            (let ([idx (extract-suffix x)])
              (when (member idx idx*)
                (errorf who "non-unique ~s suffix ~s found" what idx))
              (loop x* (cons idx idx*))))))))

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


;; pass: remove-complex-opera* 
#| output:
Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
Body    ----> (locals (uvar*) Tail)
Tail    ----> Triv
          |   (alloc Triv)
          |   (mref Triv Triv)
          |   (binop Triv Triv)
          |   (Triv Triv*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! uvar Value)
          |   (Triv Triv*)
          |   (mset! Triv Triv Triv)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Value   ----> Triv
          |   (alloc Triv)
          |   (mref Triv Triv)
          |   (binop Triv Triv)
          |   (Triv Triv*)
          |   (if Pred Value Value)
          |   (begin Effect* Value)
Triv    ----> uvar | int | label
|#
(define-who remove-complex-opera*
  (define new-local* '())
  (define (new-t)
    (let ([t (unique-name 't)])
      (set! new-local* (cons t new-local*))
      t))
  (define simple?
    (lambda (x)
      (or (uvar? x) (label? x)
          (and (integer? x) (exact? x))
          (memq x '(+ - * logand logor sra mref))
          (memq x '(= < <= > >=)))))
  (define trivialize-call
    (lambda (expr*)
      (let-values ([(set* call) (break-down-expr* expr*)]) 
        (make-begin `(,@set* ,call)))))
  (define break-down-expr*
    (lambda (expr*)
      (match expr*
        [() (values '() '())] 
        [(alloc . ,[set* rest*])
          (values set* `(alloc ,rest* ...))]
        [(mset! . ,[set* rest*])
          (values set* `(mset! ,rest* ...))]
        ;; if s is trivial or operator
        [(,s . ,[set* rest*]) (guard (simple? s))
          (values set* `(,s ,rest* ...))]
        [(,[Value -> expr] . ,[set* rest*])
          (let ([t (new-t)])
            (values `((set! ,t ,expr) ,set* ...) `(,t ,rest* ...)))])))
  (define Body
    (lambda (bd)
      (set! new-local* '())
      (match bd
        ;; Body    ----> (locals (uvar*) Tail)
        [(locals (,local* ...) ,[Tail -> tail])
          `(locals (,local* ... ,new-local* ...) ,tail)])))
  (define Tail
    (lambda (tail)
      (match tail
        ;; Tail    ----> (alloc Value)
        ;;         ====> (alloc Triv)
        [(alloc ,val)
          (trivialize-call `(alloc ,val))]
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,[Effect -> ef*] ... ,[tail-exp])
          (make-begin `(,ef* ... ,tail-exp))]
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Tail    ----> (binop Value Value)
        ;;           |   (mref Value Value)
        ;;         ====> (binop Triv Triv)
        ;;           |   (mref Triv Triv)
        [(,binop ,x ,y) (guard (memq binop '(+ - * logand logor sra mref)))
          (trivialize-call `(,binop ,x ,y))]
        ;; Tail    ----> (Value Value*)
        ;;         ====> (Triv Triv*)
        [(,rator ,rand* ...) (trivialize-call `(,rator ,rand* ...))]
        ;; Tail    ----> Triv
        [,triv triv])))
  (define Pred
    (lambda (pred)
      (match pred
        ;; Pred    ----> (true)
        [(true) '(true)]
        ;; Pred    ----> (false)
        [(false) '(false)]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[conde] ,[conseq] ,[alt])
          `(if ,conde ,conseq ,alt)]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> effect*] ... ,[tail])
          (make-begin `(,effect* ... ,tail))]
        ;; Pred    ----> (relop Value Value)
        ;;         ====> (relop Triv Triv)
        [(,relop ,x ,y) (guard (memq relop '(< <= >= = >)))
          (trivialize-call `(,relop ,x ,y))])))
  (define Effect
    (lambda (effect)
      (match effect
        ;; Effect  ----> (nop)
        [(nop) '(nop)]
        ;; Effect  ----> (set! uvar Value)
        [(set! ,unique-var ,[Value -> value])
          `(set! ,unique-var ,value)]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[ef] ,[effect*] ...)
          (make-begin `(,ef ,effect* ...))]
        ;; Effect  ----> (Value Value*)
        ;;           |   (mset! Value Value Value)
        ;;         ====> (Triv Triv*)
        ;;           |   (mset! Triv Triv Triv)
        [(,rator ,rand* ...)
          (trivialize-call `(,rator ,rand* ...))])))
  (define Value
    (lambda (val)
      (match val
        ;; Value   ----> (alloc Value)
        ;;         ====> (alloc Triv)
        [(alloc ,val)
          (trivialize-call `(alloc ,val))]
        ;; Value   ----> (begin Effect* Value)
        [(begin ,[Effect -> ef*] ... ,[val])
          (make-begin `(,ef* ... ,val))]
        ;; Value   ----> (if Pred Value Value)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Value   ----> (binop Value Value)
        ;;           |   (mref Value Value)
        ;;         ====> (binop Triv Triv)
        ;;           |   (mref Triv Triv)
        [(,binop ,x ,y) (guard (memq binop '(+ - * logand logor sra mref)))
          (trivialize-call `(,binop ,x ,y))]
        ;; Value   ----> (Value Value*)
        ;;         ====> (Triv Triv*)
        [(,rator ,rand* ...)
          (trivialize-call `(,rator ,rand* ...))]
        ;; Value   ----> Triv
        [,triv triv])))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
      [(letrec ([,label* (lambda (,fml** ...) ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)])))


;; pass: flatten-set!
;; (set! x (begin e1 ... e^n−1 e^n)) --> (begin e1 ... e^n−1 (set! x e^n))
;; (set! x (if e1 e2 e3)) --> (if e1 (set! x e2) (set! x e3))
;; remove alloc term
#| output:
Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
Body    ----> (locals (uvar*) Tail)
Tail    ----> Triv
          |   (binop Triv Triv)
          |   (Triv Triv*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
          |   (mref Triv Triv)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! uvar Triv)
          |   (set! uvar (binop Triv Triv))
          |   (set! uvar (Triv Triv*))
          |   (set! uvar (mref Triv Triv))
          |   (Triv Triv*)
          |   (mset! Triv Triv Triv)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Triv    ----> uvar | int | label
|#
(define-who flatten-set!
  (define new-local* '())
  (define new-t
    (lambda ()
      (let ([t (unique-name 't)])
        (set! new-local* (cons t new-local*))
        t)))
  (define Body
    (lambda (bd)
      (set! new-local* '())
      (match bd
        ;; Body    ----> (locals (uvar*) Tail)
        [(locals (,uvar* ...) ,[Tail -> tail])
          `(locals (,uvar* ... ,new-local* ...) ,tail)])))
  (define Tail
    (lambda (tail)
      (match tail
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,[Effect -> ef*] ... ,[tail-exp])
          (make-begin `(,ef* ... ,tail-exp))]
        ;; alloc returns the allocated address, 
        ;; rdx skips the allocated size and points to the next address.
        ;; Tail    ----> (alloc Triv)
        ;;         ====> (begin (set! uvar rdx)
        ;;                 (set! rdx (+ rdx Triv)) uvar)
        [(alloc ,val)
          (let ([t (new-t)])
            `(begin (set! ,t ,allocation-pointer-register)
              (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,val))
              ,t))]
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Tail    ----> Triv
        ;;           |   (binop Triv Triv)
        ;;           |   (Triv Triv*)
        ;;           |   (mref Triv Triv)
        [,other other])))
  (define Pred
    (lambda (pred)
      (match pred
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[conde] ,[conseq] ,[alt])
          `(if ,conde ,conseq ,alt)]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> effect*] ... ,[tail])
          (make-begin `(,effect* ... ,tail))]
        ;; Pred    ----> (relop Triv Triv)
        ;;           |   (true)
        ;;           |   (false)
        [,other other])))
  (define Effect
    (lambda (effect)
      (match effect
        ;; Effect  ----> (set! uvar Value)
        ;;         ====> (set! uvar Triv)
        ;;           |   (set! uvar (binop Triv Triv))
        ;;           |   (set! uvar (Triv Triv*))
        ;;           |   (set! uvar (mref Triv Triv))
        [(set! ,unique-var ,expr)
          (Value unique-var expr)]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[ef] ,[effect*] ...) 
          (make-begin `(,ef ,effect* ...))]
        ;; Effect  ----> (Triv Triv*)
        ;;           |   (nop)
        ;;           |   (mset! Triv Triv Triv)
        [,other other])))
  (define Value
    (lambda (var expr)
      (match expr
        ;; Value   ----> (begin Effect* Value)
        ;;         ====> (begin Effect* (set! var triv))
        [(begin ,[Effect -> ef*] ... ,[val])
          (make-begin `(,ef* ... ,val))]
        ;; Value   ----> (if Pred Value Value)
        ;;         ====> (if Pred (set! var triv1) (set! var triv2))
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Value   ----> (alloc Triv)
        [(alloc ,val)
          `(begin (set! ,var ,allocation-pointer-register)
            (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,val)))]
        ;; Value   ----> Triv
        ;;           |   (binop Triv Triv)
        ;;           |   (mref Triv Triv)
        ;;           |   (Triv Triv*)
        [,x `(set! ,var ,x)])))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
      [(letrec ([,label* (lambda (,fml** ...) ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)])))


;; pass: impose-calling-conventions
;; output:
#|
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locals (uvar*) (new-frames (Frame*) Tail))
Frame   ----> (uvar*)
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Triv Triv Triv)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
;; 由 (lambda (param*) Body) 转变成 (lambda () Body) 的必要操作是将 参数的值 赋给 参数变量
;; 其中 param* 在这里是 fml*，这时在寄存器 r8、r9 与 frame-var 中存储着 参数的值
;; 所以由 argument-locations 函数找出 参数的值 存储在哪些寄存器中
;; 然后将 这些寄存器的值 赋给 参数变量，在使用时需要将参数的真实值赋给供存储的寄存器
;; 每个程序最后都要跳转到 r15 从而返回到运行时系统，所以最开始需要将 r15 的地址保存在 rp.n 中
;; 在其他函数调用时，如果是当前函数的末尾，那么将 rp.n 重新赋给 r15，这样还原了 r15 的值好给下一个函数使用
;; 但是如果是过程中调用了其他函数，那么可以将该调用之后的操作用一个 rp$n 的 label 作为函数名来构造一个新函数
;; rp$n 这个函数名赋给 r15 寄存器，那么在函数调用完成后返回 r15 就又返回了 rp$n 位置了
;; 这个位置恰好就是过程中 之后的操作部分
;; rax 保存着函数最后表达式的值，它唯一能被用到的地方是 (set! ,uvar (,triv ,triv* ...)) 表达式中
;; 因为使用到函数的调用，所以这时这时需要使用函数调用的结果，这个结果就保存在 rax 中
;; Effect 中的 (Triv Triv*) 表达式中参数不能将值直接赋给寄存器与从 0 开始的 frame-var，因为返回之后可能会继续用到之前的参数
;; 这时寄存器或者从 0 开始的 frame-var 的值就被 (Triv Triv*) 所覆盖了。所以 (Triv Triv*) 中参数的值需要赋给寄存器与
;; 最大的 frame-var 索引加 1 所得到的 frame-var，这里临时用 index->new-frame-var 来替代。
(define-who impose-calling-conventions
  ;; stores all the nfv assignments
  (define new-frame-var** '())
  (define new-frame-var* '())
  (define index->new-frame-var
    (lambda (idx)
      (let ([nfv (unique-name 'nfv)])
        (set! new-frame-var* (append new-frame-var* `(,nfv)))
        nfv)))
  ;; r8 , r9 , fvn ...
  (define argument-locations
    (lambda (fmls idx->fv)
      (let f ([fmls fmls]
              [regs parameter-registers]
              [fv-idx 0])
        (cond
          [(null? fmls) '()]
          [(null? regs)
            (cons (idx->fv fv-idx) (f (cdr fmls) regs (add1 fv-idx)))]
          [else (cons (car regs) (f (cdr fmls) (cdr regs) fv-idx))]))))
  (define trivial?
    (lambda (x)
      (or (uvar? x) (integer? x) (label? x))))
  (define Tail
    (lambda (rp)
      (lambda (tail)
        (match tail
          ;; Tail    ----> (begin Effect* Tail)
          [(begin ,[Effect -> ef*] ... ,[tail-exp])
            (make-begin `(,ef* ... ,tail-exp))]
          ;; Tail    ----> (if Pred Tail Tail)
          [(if ,[Pred -> pred] ,[conseq] ,[alt])
            `(if ,pred ,conseq ,alt)]
          ;; Tail    ----> (binop Triv Triv)
          ;;           |   (mref Triv Triv)
          ;;         ====> (begin (set! rax (binop Triv Triv)) (rp rbp rax))
          ;;           |   (begin (set! rax (mref Triv Triv)) (rp rbp rax))
          [(,op ,rand1 ,rand2) (guard (memq op '(+ - * logand logor sra mref)))
            (let ([return-value-expr `(set! ,return-value-register (,op ,rand1 ,rand2))]
                  [return-calling-expr `(,rp ,frame-pointer-register ,allocation-pointer-register ,return-value-register)])
              `(begin ,return-value-expr ,return-calling-expr))]
          ;; Tail    ----> (Triv Triv*)
          ;;         ====> (begin (set! loc* triv*) ... (set! r15 rp) (triv r15 rbp loc* ...))
          [(,triv ,triv* ...)
            (let ([fml-loc* (argument-locations triv* index->frame-var)])
              `(begin (set! ,fml-loc* ,triv*) ... (set! ,return-address-register ,rp)
                (,triv ,return-address-register ,frame-pointer-register ,allocation-pointer-register ,@fml-loc*)))]
          ;; Tail    ----> Triv
          ;;         ====> (begin (set! rax triv) (rp rbp rax))
          [,triv
            (let ([return-value-expr `(set! ,return-value-register ,triv)]
                  [return-calling-expr `(,rp ,frame-pointer-register ,allocation-pointer-register ,return-value-register)])
              `(begin ,return-value-expr ,return-calling-expr))]))))
  (define Pred
    (lambda (pred)
      (match pred
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[conde] ,[conseq] ,[alt])
          `(if ,conde ,conseq ,alt)]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> effect*] ... ,[tail])
          (make-begin `(,effect* ... ,tail))]
        ;; Pred    ----> (relop Triv Triv)
        ;;           |   (true)
        ;;           |   (false)
        [,other other])))
  (define Effect
    (lambda (effect)
      (match effect
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> pred] ,[conseq] ,[alt])
          `(if ,pred ,conseq ,alt)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[ef] ,[effect*] ...)
          (make-begin `(,ef ,effect* ...))]
        ;; Effect  ----> (set! uvar (Triv Triv*))
        ;;         ====> (begin Effect* (set! uvar rax))
        [(set! ,uvar (,triv ,triv* ...)) (guard (trivial? triv))
          (make-begin `(,(Effect `(,triv ,triv* ...)) (set! ,uvar ,return-value-register)))]
        ;; Effect  ----> (set! uvar (binop Triv Triv))
        ;;           |   (set! uvar Triv)
        ;;           |   (set! uvar (mref Triv Triv))
        [(set! ,other ...)
          `(set! ,other ...)]
        ;; Effect  ----> (mset! Triv Triv Triv)
        [(mset! ,base ,offset ,val) `(mset! ,base ,offset ,val)]
        ;; Effect  ----> (nop)
        [(nop) '(nop)]
        ;; Effect  ----> (Triv Triv*)
        ;;         ====> (return-point rp-label (begin (set! loc* triv*) ... (set! r15 rp-label) (triv r15 rbp loc* ...)))
        [(,triv ,triv* ...)
          (set! new-frame-var* '())
          (let* ([return-point-var (unique-label 'rp)]
                 [fml-loc* (argument-locations triv* index->new-frame-var)]
                 [expr `(begin (set! ,fml-loc* ,triv*) ...
                        (set! ,return-address-register ,return-point-var)
                        (,triv ,return-address-register ,frame-pointer-register ,allocation-pointer-register ,@fml-loc*))])
            (set! new-frame-var** (cons new-frame-var* new-frame-var**))
            `(return-point ,return-point-var ,expr))])))
  (define Body
    (lambda (bd fml*)
      (set! new-frame-var** '())
      (let ([rp (unique-name 'rp)])
        (match bd
          ;; Body    ----> (locals (uvar*) Tail)
          ;;         ====> (locals (uvar*) (new-frames (Frame*) Tail))
          ;; Frame   ====> (uvar*)
          [(locals (,local* ...) ,[(Tail rp) -> tail])
            (let ([fml-loc* (argument-locations fml* index->frame-var)])
              `(locals (,rp ,fml* ... ,local* ... ,new-frame-var** ... ...)
                (new-frames (,new-frame-var** ...)
                  ,(make-begin
                    `((set! ,rp ,return-address-register)
                      (set! ,fml* ,fml-loc*) ...
                      ,tail)))))]))))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda (uvar*) Body)]*) Body)
      ;;         ====> (letrec ([label (lambda () Body)]*) Body)
      [(letrec ([,label* (lambda (,fml** ...) ,bd*)] ...) ,bd)
        (let* ([bd* (map Body bd* fml**)]
               [bd (Body bd '())])
          `(letrec ([,label* (lambda () ,bd*)] ...) ,bd))])))


;; pass: uncover-frame-conflict
;; This section of the code simply prepares a live-set i.e the set of variables live before an assignment instruction is encountered
;; The update conflict table is responsible for updating the conflict table ct using side effects
;; if fv0 is current Lhs and {a.1 b.2 c.3} is live set we add the live-set to fv0's conflict
;; For an if-instruction encountered we take the union of both the conseqent and alternative parts and combine it
;; Processing of this code goes in a bottom up manner, since a frame can't conflict with a register only variables would be present in the conflict set
;; output:
#|
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locals (uvar*) (new-frames (Frame*)
                (spills (uvar*)
                  (frame-conflict conflict-graph
                    (call-live (uvar/fvar*) Tail)))))
Frame   ----> (uvar*)
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Triv Triv Triv)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
;; 这是使用 Live Analysis 方法来
;; call-live 保存了 Effect 的 (Triv Triv*) 子句之后被使用到的变量或者 frame-var
;; 之后给 (Triv Triv*) 调用的参数匹配寄存器与 frame-var 的时候从 call-live 中序号最大的 frame-var 开始分配
(define-who uncover-frame-conflict
  (define add-conflicts!
    (lambda (ct lhs live*)
      (define add-ct!
        (lambda (var1 var2)
          (if (not (eq? var1 var2))
              (let ([a (assq var1 ct)])
                (set-cdr! a (set-cons var2 (cdr a)))))))
      (when (uvar? lhs)
        (for-each
          (lambda (live) (add-ct! lhs live))
          live*))
      (for-each
        (lambda (live)
          (when (and (uvar? live) (not (register? lhs)))
            (add-ct! live lhs)))
        live*)))
  (define call-live* '())
  (define Body
    (lambda (x)
      (set! call-live* '())
      (match x
        ;; Body    ----> (locals (uvar*) (new-frames (Frame*) Tail))
        ;;         ====> (locals (uvar*) (new-frames (Frame*)
        ;;                (spills (uvar*)
        ;;                  (frame-conflict conflict-graph
        ;;                    (call-live (uvar/fvar*) Tail)))))
        [(locals (,uvar* ...) (new-frames (,nfv** ...) ,tail))
          (let ([ct (map (lambda (x) (cons x '())) uvar*)])
            (let ([uvar* (filter uvar? (Tail tail ct))])
              (unless (null? uvar*)
                (errorf who "found variables ~s live on entry" uvar*)))
            (let ([spill* (filter uvar? call-live*)])
              `(locals (,(difference uvar* spill*) ...)
                (new-frames (,nfv** ...)
                  (spills ,spill* 
                    (frame-conflict ,ct 
                      (call-live (,call-live* ...) ,tail)))))))])))
  (define Tail
    (lambda (x ct) 
      (match x
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,test ,[c-live*] ,[a-live*])
          (Pred test c-live* a-live* ct)]
        ;; Tail    ----> (Triv Loc*)
        [(,[Triv -> target] ,[Triv -> live*] ...)
          `(,target ... ,live* ... ...)])))
  (define Triv
    (lambda (x)
      (if (or (uvar? x) (frame-var? x)) `(,x) '())))
  ;; from back to front
  (define Effect*
    (lambda (x live* ct)
      (match x
        [() live*]
        [(,ef* ... ,ef) (Effect* ef* (Effect ef live* ct) ct)])))
  (define Effect
    (lambda (x live* ct)
      (match x
        ;; Effect  ----> (nop)
        [(nop) live*]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,test ,[c-live*] ,[a-live*])
          (Pred test  c-live* a-live* ct)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        ;; Effect  ----> (set! Var (binop Triv Triv))
        [(set! ,lhs (,binop ,[Triv -> x-live*] ,[Triv -> y-live*]))
          (guard (memq binop '(+ - * logand logor)))
          (add-conflicts! ct lhs live*)
          (union x-live* y-live* (remq lhs live*))]
        ;; Effect  ----> (set! Var (mref Triv Triv))
        [(set! ,lhs (mref ,[Triv -> x-live*] ,[Triv -> y-live*]))
          (add-conflicts! ct lhs (union x-live* y-live* live*))
          (union x-live* y-live* (remq lhs live*))]
        ;; Effect  ----> (mset! Triv Triv Triv)
        [(mset! ,[Triv -> base] ,[Triv -> offset] ,[Triv -> value])
          (if (not (null? base))
              (add-conflicts! ct (car base) (union offset value live*)))
          (if (not (null? offset))
              (add-conflicts! ct (car offset) (union base value live*)))
          (if (not (null? value))
              (add-conflicts! ct (car value) (union offset base live*)))
          (union base offset value live*)]
        ;; Effect  ----> (set! Var Triv)
        [(set! ,lhs ,[Triv -> var*])
          (add-conflicts! ct lhs live*)
          (union var* (remq lhs live*))]
        ;; Effect  ----> (return-point label Tail)
        [(return-point ,rplab ,tail)
          (let ([new-live* (Tail tail ct)])
            ;; 在 return-point 时仍然 live 的集合就是 call-live 的
            (set! call-live* (union call-live* live*))
            (union live* new-live*))])))
  (define Pred
    (lambda (x t-live* f-live* ct)
      (match x
        ;; Pred    ----> (true)
        [(true) t-live*]
        ;; Pred    ----> (false)
        [(false) f-live*]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,test ,[c-live*] ,[a-live*])
          (union t-live* f-live* (Pred test c-live* a-live* ct))]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        ;; Pred    ----> (relop Triv Triv)
        [(,predop ,[Triv -> x-live*] ,[Triv -> y-live*])
          (remove-nulls (union x-live* y-live* t-live* f-live*))])))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda () Body)]*) Body)
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; pass: pre-assign-frame
#| output:
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locals (uvar*)
                (new-frames (Frame*)
                  (locate ([uvar fvar]*)
                    (frame-conflict conflict-graph
                      (call-live (uvar/fvar*) Tail)))))
Frame   ----> (uvar*)
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Triv Triv Triv)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
;; spill* 保存的是 Effect 的 (Triv Triv*) 子句之后的变量 uvars
;; 该 pass 处理 spill* 。等同于给 Effect 的 (Triv Triv*) 子句之后的变量绑定 frame-var
;; (Triv Triv*) 调用中参数的值的绑定的 frame-var 必须大于该句之后最大的 frame-var
;; 所以先给 (Triv Triv*) 子句之后的变量绑定 frame-var，然后下一次就可以从
;; (Triv Triv*) 子句之后的全部 frame-var 与这次绑定的 frame-var 中一起取最大的 frame-var 开始构造。
(define-who pre-assign-frame
  (define alt-uvars
    (lambda (conflict* home*)
      (cond
        [(null? conflict*) '()]
        [(frame-var? (car conflict*))
          (set-cons (car conflict*) (alt-uvars (cdr conflict*) home*))]
        [(assq (car conflict*) home*) =>
          (lambda (x) (set-cons (cadr x) (alt-uvars (cdr conflict*) home*)))]
        [else (alt-uvars (cdr conflict*) home*)])))
  (define find-frame-var
    (lambda (used*)
      (let f ([index 0])
        (let ([fv (index->frame-var index)])
          (if (memq fv used*)
              (f (add1 index))
              fv)))))
  (define find-homes
    (lambda (var* ct home*)
      (if (null? var*)
          home*
          (let* ([var (car var*)]
                 [conflict* (cdr (assq var ct))]
                 [home (find-frame-var (alt-uvars conflict* home*))])
            (find-homes (cdr var*) ct (cons `(,var ,home) home*))))))
  (define Body
    (lambda (body)
      (match body
        ;; Body    ----> (locals (uvar*) (new-frames (Frame*)
        ;;                 (spills (uvar*)
        ;;                   (frame-conflict conflict-graph
        ;;                     (call-live (uvar/fvar*) Tail)))))
        ;;         ====> (locals (uvar*) (new-frames (Frame*)
        ;;                 (locate ([uvar fvar]*)
        ;;                   (frame-conflict conflict-graph
        ;;                     (call-live (uvar/fvar*) Tail)))))
        [(locals (,local* ...)
           (new-frames (,nfv** ...)
             (spills (,spill* ...)
               (frame-conflict ,ct
                 (call-live (,call-live* ...) ,tail)))))
          (let ([home* (find-homes spill* ct '())])
            `(locals (,local* ...)
              (new-frames (,nfv** ...)
                (locate (,home* ...)
                  (frame-conflict ,ct
                    (call-live (,call-live* ...) ,tail))))))])))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda () Body)]*) Body)
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))



;; pass: assign-new-frame
#| output:
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locals (uvar*)
                (ulocals ()
                  (locate ([uvar fvar]*)
                    (frame-conflict conflict-graph Tail))))
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Triv Triv Triv)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
;; 在 Effect 的 (Triv Triv*) 子句前后需要改变帧指针的位置
;; 这样到调用到 (Triv Triv*) 子句的时候，取出的参数就不会覆盖之前语句块中
;; 需要的 frame-var 的值，在调用完成之后需要将帧指针的位置还原。
(define-who assign-new-frame
  (define find-max
		(lambda (ls)
			(cond
				[(null? ls) '-1 ]
				[else (max (car ls) (find-max (cdr ls)))])))
  (define frame-size
    (lambda (call-live* home*)
      (let ([ls (map (lambda (x)
                       (if (frame-var? x)
                           (frame-var->index x)
                           (frame-var->index (cadr (assq x home*)))))
                  call-live*)])
        (add1 (find-max ls)))))
  (define do-assign
    (lambda (fs)
      (lambda (var*)
        (let f ([index fs] [ls var*] [rs '()])
          (let ([fv (index->frame-var index)])
            (cond
              [(null? ls) rs]
              [else (f (add1 index) (cdr ls) (cons `(,(car ls) ,fv) rs))]))))))
  (define Body
    (lambda (x)
      (match x
        ;; Body    ----> (locals (uvar*)
        ;;                 (new-frames (Frame*)
        ;;                   (locate ([uvar fvar]*)
        ;;                     (frame-conflict conflict-graph
        ;;                       (call-live (uvar/fvar*) Tail)))))
        ;;         ====> (locals (uvar*)
        ;;                 (ulocals ()
        ;;                   (locate ([uvar fvar]*)
        ;;                     (frame-conflict conflict-graph Tail))))
        [(locals (,local* ...)
           (new-frames (,nfv** ...)
             (locate (,home* ...)
               (frame-conflict ,ct
                 (call-live (,call-live* ...) ,tail)))))
          (let ([fs (frame-size call-live* home*)])
                    ;; local* - nfv**
           `(locals ,(difference local* `(,nfv** ... ...))
             (ulocals ()
               (locate (,home* ... ,(map (do-assign fs) nfv**) ... ...)
                 (frame-conflict ,ct ,((Tail fs) tail))))))])))
  (define Tail
    (lambda (fs)
      (lambda (x)
        (match x
          ;; Tail    ----> (if Pred Tail Tail)
          [(if ,[(Pred fs) -> test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Tail    ----> (begin Effect* Tail)
          [(begin ,[(Effect fs) -> ef*] ... ,[tail])
            (make-begin `(,ef* ... ,tail))]
          ;; Tail    ----> (Triv Loc*)
          [,other other]))))
  (define Pred
    (lambda (fs)
      (lambda (x)
        (match x
          ;; Pred    ----> (if Pred Pred Pred)
          [(if ,[test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Pred    ----> (begin Effect* Pred)
          [(begin ,[(Effect fs) -> ef*] ... ,[pr])
            (make-begin `(,ef* ... ,pr))]
          ;; Pred    ----> (true)
          ;;           |   (false)
          ;;           |   (relop Triv Triv)
          [,other other]))))
  (define Effect
    (lambda (fs)
      (lambda (x)
        (match x
          ;; Effect  ----> (if Pred Effect Effect)
          [(if ,[(Pred fs) -> test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Effect  ----> (begin Effect* Effect)
          [(begin ,[ef*] ... ,[ef])
            (make-begin `(,ef* ... ,ef))]
          ;; Effect  ----> (return-point label Tail)
          ;;         ====> (begin (set! rbp (+ rbp fs*8))
          ;;                 (return-point label Tail)
          ;;                   (set! rbp (- rbp fs*8)))
          [(return-point ,rplab ,[(Tail fs) -> tail])
            `(begin (set! ,frame-pointer-register (+ ,frame-pointer-register ,(ash fs align-shift)))
              (return-point ,rplab ,tail)
              (set! ,frame-pointer-register (- ,frame-pointer-register ,(ash fs align-shift))))]
          ;; Effect  ----> (nop)
          ;;           |   (set! Var Triv)
          ;;           |   (set! Var (binop Triv Triv))
          ;;           |   (set! Var (mref Triv Triv))
          ;;           |   (mset! Triv Triv Triv)
          [,other other]))))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda () Body)]*) Body)
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; pass: finalize-frame-locations
;; replaces all variables that have been allocated a frame with the appropriate frame variables.
;; 替换所有 uvar 到 frame-var 或者 register
(define-who finalize-frame-locations
  (define Body
    (lambda (bd)
      (match bd
        ;; Body    ----> (locals (uvar*)
        ;;                 (ulocals (ulocal*)
        ;;                   (locate ([uvar fvar]*)
        ;;                     (frame-conflict conflict-graph Tail))))
        [(locals (,local* ...)
          (ulocals (,ulocal* ...)
            (locate ([,uvar* ,loc*] ...)
              (frame-conflict ,ct ,[(Tail (map cons uvar* loc*)) -> tail]))))
          `(locals ,local*
            (ulocals (,ulocal* ...)
              (locate ([,uvar* ,loc*] ...)
                (frame-conflict ,ct ,tail))))]
        ;; Body    ----> (locate ([uvar loc]*) ,tail)
        [(locate ([,uvar* ,loc*] ...) ,tail)
          `(locate ([,uvar* ,loc*] ...) ,tail)])))
  (define Tail
    (lambda (env)
      (lambda (x)
        (match x
          ;; Tail    ----> (begin Effect* Tail)
          [(begin ,[(Effect env) -> effect*] ... ,[tail])
            (make-begin `(,effect* ... ,tail))]
          ;; Tail    ----> (if Pred Tail Tail)
          [(if ,[(Pred env) -> test] ,[tail1] ,[tail2])
            `(if ,test ,tail1 ,tail2)]
          ;; Tail    ----> (Triv Loc*)
          [(,[(Triv env) -> loc*] ...) `(,loc* ...)]))))
  (define Effect
    (lambda (env)
      (lambda (effect)
        (match effect
          ;; Effect  ----> (nop)
          [(nop) '(nop)]
          ;; Effect  ----> (begin Effect* Effect)
          [(begin ,[effect] ,[effect*] ...)
            (make-begin `(,effect ,effect* ...))]
          ;; Effect  ----> (set! Var (binop Triv Triv))
          ;;           |   (set! Var (mref Triv Triv))
          [(set! ,[(Var env) -> var] (,binop ,[(Triv env) -> triv1] ,[(Triv env) -> triv2]))
            `(set! ,var (,binop ,triv1 ,triv2))]
          ;; Effect  ----> (mset! Triv Triv Triv)
          [(mset! ,[(Var env) -> base] ,[(Var env) -> offset] ,[(Var env) -> value])
            `(mset! ,base ,offset ,value)]
          ;; Effect  ----> (set! Var Triv)
          [(set! ,[(Var env) -> var] ,[(Triv env) -> triv])
            `(set! ,var ,triv)]
          ;; Effect  ----> (if Pred Effect Effect)
          [(if ,[(Pred env) -> test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Effect  ----> (return-point label Tail)
          [(return-point ,rplab ,[(Tail env) -> tail])
            `(return-point ,rplab ,tail)]))))
  (define Pred
    (lambda (env)
      (lambda (x)
        (match x
          ;; Pred    ----> (begin Effect* Pred)
          [(begin ,[(Effect env) -> effect*] ... ,[pred])
            (make-begin `(,effect* ... ,pred))]
          ;; Pred    ----> (if Pred Pred Pred)
          [(if ,[test] ,[conseq] ,[alt])
            `(if ,test ,conseq ,alt)]
          ;; Pred    ----> (relop Triv Triv)
          [(,relop ,[(Triv env) -> triv1] ,[(Triv env) -> triv2])
            `(,relop ,triv1 ,triv2)]
          ;; Pred    ----> (true)
          ;;           |   (false)
          [,other other]))))
  (define Triv
    (lambda (env)
      (lambda (x)
        (if (or (integer? x)
                (label? x))
            x
            ((Var env) x)))))
  (define Var
    (lambda (env)
      (lambda (v)
        (cond
          [(and (uvar? v) (assq v env)) => cdr]
          [else v]))))
  (lambda (x)
    (match x
      ;; Program ----> (letrec ([label (lambda () Body)]*) Body)
      [(letrec ([,label* (lambda () ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)])))


;; pass: select-instructions
;; select-instructions does a signifcant rewrite of the code where necessary, the x86-64 architecture imposes certian limitations on the instructions
;; we are allowed to use, but the same cant be imposed on a programmer who writes programs, the select-instructions pass converts certian blocks of codes which may
;; be incompatible by x-86-64 instruction standards to a compatible form, the bulk of the rewrite has to be done when instructions of the form (set! x y) or
;; (set! x (op y z)) are encountered, another place where a rewrite would be neccesary is the place where we have relational operators
;; eg (set! fv0 rax) is converted to ((set! u.1 fv0) (set! u.1 rax)) because the mov expression only allows us to move a value to register location as 
;; Body −--> (locals (uvar*)
;;             (ulocals (uvar*)
;;               (locate ([uvar fvar]*)
;;                 (frame-conflict conflict-graph Tail))))
;;       | (locate ([uvar Loc]*) Tail)
(define-who select-instructions
  (define relop^
    (lambda (op)
      (case op
        ['> '<]
        ['< '>]
        ['<= '>=]
        ['= '=])))
  (define ur?
    (lambda (x)
      (or (register? x)
          (uvar? x))))
  (define new-ulocal* '())
  (define int64-or-label?
    (lambda (x)
      (or (and (not (int32? x))
               (int64? x))
          (label? x))))
  (define new-u
    (lambda ()
      (let ([u (unique-name 't)])
        (set! new-ulocal* (cons u new-ulocal*))
        u)))
  (define select-relop
    (lambda (relop x y)
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
      (cond
        [(and (int32? x) (or (ur? y) (frame-var? y)))
          `(,(relop^ relop) ,y ,x)]
        [(or (and (frame-var? x) (frame-var? y))
             (and (int32? x) (int32? y))
             (and (int64-or-label? x) (or (ur? y)
                                          (frame-var? y)
                                          (int32? y))))
          (let ([u (new-u)])
            `(begin (set! ,u ,x) (,relop ,u ,y)))]
        [(and (or (ur? x) (frame-var? x) (int32? x))
              (int64-or-label? y))
          (let ([u (new-u)])
            `(begin (set! ,u ,y) (,(relop^ relop) ,u ,x)))]
        [(and (int64-or-label? x) (int64-or-label? y))
          (let ([u1 (new-u)] [u2 (new-u)])
            `(begin (set! ,u1 ,x) (set! ,u2 ,y) (,relop ,u1 ,u2)))]
        [else `(,relop ,x ,y)])))
  (define select-binop
    (lambda (var binop x y)
      (cond
        [(eq? var x) (select-binop-2 binop var y)]
        [(eq? var y) (select-binop-2 binop var x)]
        [else
          (let ([u (new-u)])
            (make-begin `((set! ,u ,x) ,(select-binop-2 binop u y) (set! ,var ,u))))])))
  (define select-binop-2
    (lambda (binop x y)
      ;; x <- v1, v2
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
      (cond
        [(and (member binop '(- + sra logor logand))
              (or (int64-or-label? y)
                  (and (frame-var? x)
                       (frame-var? y))))
          (let ([u (new-u)])
            `(begin (set! ,u ,y) (set! ,x (,binop ,x ,u))))]
        [(and (eq? binop '*)
              (ur? x)
              (int64-or-label? y))
          (let ([u (new-u)])
            `(begin (set! ,u ,y) (set! ,var (,binop ,x ,u))))]
        [(and (eq? binop '*)
              (ur? x)
              (int64-or-label? y))
          (let ([u (new-u)])
            `(begin (set! ,u ,y) (set! ,x (,binop ,x ,u))))]
        [else `(set! ,x (,binop ,x ,y))])))
  (define select-move
    (lambda (x y)
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
      (cond
        [(and (frame-var? x)
              (or (frame-var? y)
                  (int64-or-label? y)))
          (let ([u (new-u)])
            `(begin (set! ,u ,y) (set! ,x ,u)))]
        [else `(set! ,x ,y)])))
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
      (cond
        [(and (ur? base)
              (or (integer? offset)
                  (ur? offset)))
          `(set! ,lhs (mref ,base ,offset))]
        [(ur? base)
          (let ([u (new-u)])
            `(begin (set! ,u ,offset) 
              (set! ,lhs (mref ,base ,u))))]
        [(and (not (ur? base))
              (integer? offset))
          (let ([u (new-u)])
            `(begin (set! ,u ,base)
              (set! ,lhs (mref ,u ,offset))))]
        [(and (ur? offset)
              (or (integer? base)
                  (frame-var? base)))
          (select-mref lhs offset base)]
        [else (let ([u1 (new-u)]
                    [u2 (new-u)])
                `(begin (set! ,u1 ,base) (set! ,u2 ,offset)
                  (set! ,lhs (mref ,u1 ,u2))))])))
  ;; select mref and mset do the same thing the only difference being that 
  ;; the former returns mref expressions and the latter returns mset!
  (define select-mset
    (lambda (base offset value)
      (cond
        [(and (ur? base)
              (or (integer? offset)
                  (ur? offset)))
          `(mset! ,base ,offset ,value)]
        [(ur? base)
          (let ([u (new-u)])
            `(begin (set! ,u ,offset) 
              (mset! ,base ,u ,value)))]
        [(and (not (ur? base))
              (integer? offset))
          (let ([u (new-u)])
            `(begin (set! ,u ,base)
              (mset! ,u ,offset ,value) (set! ,base ,u)))]
        [(and (ur? offset)
              (or (integer? base)
                  (frame-var? base)))
          (select-mset offset base value)]
        [else (let ([u1 (new-u)]
                    [u2 (new-u)])
                `(begin (set! ,u1 ,base) (set! ,u2 ,offset)
                  (mset! ,u1 ,u2 ,value)))])))
  (define Body
    (lambda (x)
      (set! new-ulocal* '())
      (match x
        ;; Body    ----> (locals (uvar*)
        ;;                 (ulocals (ulocal*)
        ;;                   (locate ([uvar fvar]*)
        ;;                     (frame-conflict conflict-graph Tail))))
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate (,home* ...)
               (frame-conflict ,ct ,[Tail -> tail]))))
          `(locals (,local* ...)
            (ulocals (,ulocal* ... ,new-ulocal* ...)
              (locate (,home* ...)
                (frame-conflict ,ct ,tail))))]
        ;; Body    ----> (locate ([uvar loc]*) ,tail)
        [(locate (,home* ...) ,tail)
          `(locate (,home* ...) ,tail)])))
  (define Tail
    (lambda (x)
      (match x
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
          (make-begin `(,ef* ... ,tail))]
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,[Pred -> pred] ,[Tail -> conseq] ,[Tail -> alt])
          `(if ,pred ,conseq ,alt)]
        ;; Tail    ----> (Triv Loc*)
        [,other other])))
  (define Pred
    (lambda (x)
      (match x
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,[Effect -> effect*] ... ,[pred])
          (make-begin `(,effect* ... ,pred))]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,[test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Pred    ----> (relop Triv Triv)
        [(,relop ,conseq ,alt)
          (select-relop relop conseq alt)]
        ;; Pred    ----> (true)
        ;;           |   (false)
        [,other other])))
  (define Effect
    (lambda (x)
      (match x
        ;; Effect  ----> (nop)
        [(nop) '(nop)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,[effect] ,[effect*] ...)
          (make-begin `(,effect ,effect* ...))]
        ;; Effect  ----> (set! Var (mref Triv Triv))
        [(set! ,lhs (mref ,base ,offset))
          (cond
            [(ur? lhs) (select-mref lhs base offset)]
            [(frame-var? lhs)
              (let ([u (new-u)])
                (make-begin `((set! ,u ,lhs) 
                              ,(select-mref u base offset) 
                              (set! ,lhs ,u))))]
            [(label? lhs)
              (let ([u (new-u)])
                (make-begin `((set! ,u ,lhs) 
                              ,(select-mref u base offset))))])]
        ;; Effect  ----> (mset! Triv Triv Triv)
        ;;         ====> (mset! Var Var Var)
        [(mset! ,base ,offset ,value)
          (cond
            [(or (ur? value) (integer? value))
              (select-mset base offset value)]
            [(frame-var? value)
              (let ([u (new-u)])
                (make-begin `((set! ,u ,value) 
                              ,(select-mset base offset u) 
                              (set! ,value ,u))))]
            [(label? value)
              (let ([u (new-u)])
                (make-begin `((set! ,u ,value) 
                              ,(select-mset base offset u))))])]
        ;; Effect  ----> (set! Var (binop Triv Triv))
        [(set! ,lhs (,binop ,x ,y))
          (select-binop lhs binop x y)]
        ;; Effect  ----> (set! Var Triv)
        [(set! ,lhs ,rhs)
          (select-move lhs rhs)]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        ;; Effect  ----> (return-point label Tail)
        [(return-point ,rplab ,[Tail -> tail])
          `(return-point ,rplab ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; pass: uncover-register-conflict
;; This pass inserts into the output a conflict graph listing for each uvar in the locals list a list of the other
;; unique variables and registers with which it conflicts, i.e., with which it cannot share a register. It makes no
;; other changes to the program.
(define-who uncover-register-conflict
  (define add-conflicts!
    (lambda (ct lhs live*)
      (define add-conflict!
        (lambda (v1 v2)
          (if (not (eq? v1 v2))
            (let ([a (assq v1 ct)])
              (set-cdr! a (set-cons v2 (cdr a)))))))
      (when (uvar? lhs)
        (for-each
          (lambda (live)
            (add-conflict! lhs live))
          live*))
      (for-each
        (lambda (live)
          (when (and (uvar? live) 
                     (not (frame-var? lhs)))
            (add-conflict! live lhs)))
        live*)))
  (define Body
    (lambda (x)
      (match x
        [(locals (,local* ...)
          (ulocals (,ulocal* ...)
            (locate (,home* ...)
              (frame-conflict ,fv-ct ,tail))))
          ;; set up the conflict table ct for storing conflicts
          (let ([ct (map (lambda (x) (cons x '())) (append local* ulocal*))])
            (Tail tail ct)
            `(locals ,local*
              (ulocals ,ulocal*
                (locate ,home*
                  (frame-conflict ,fv-ct
                    (register-conflict ,ct ,tail))))))]
        [(locate (,home* ...) ,tail) `(locate ,home* ,tail)])))
  (define Tail
    (lambda (x ct) 
      (match x 
        [(begin ,ef* ... ,[live*])
          (Effect* ef* live* ct)]
        [(if ,test ,[c-live*] ,[a-live*])
          (Pred test c-live* a-live* ct)]
        [(,[Triv -> target] ,[Triv -> live*] ...)
          (remove-nulls (cons target live*))])))
  (define Triv
    (lambda (x)
      (if (or (register? x) (uvar? x)) x '())))
  (define Effect
    (lambda (x live* ct)
      (match x
        [(nop) live*]
        [(if ,test ,[c-live*] ,[a-live*])
          (Pred test c-live* a-live* ct)]
        [(begin ,ef* ... ,[live*])
          (Effect* ef* live* ct)]
        [(set! ,lhs (mref ,[Triv -> x-live] ,[Triv -> y-live]))
          (add-conflicts! ct lhs (set-cons x-live (set-cons y-live live*)))
          (set-cons x-live (set-cons y-live (remq lhs live*)))]
        [(mset! ,[Triv -> base] ,[Triv -> offset] ,[Triv -> value])
          (if (not (null? base)) (add-conflicts! ct base (union `(,offset) `(,value) live*)))
          (if (not (null? offset)) (add-conflicts! ct offset (union `(,base) `(,value) live*)))
          (if (not (null? value)) (add-conflicts! ct value (union `(,base) `(,offset) live*)))
          (union `(,base) `(,offset) `(,value) live*)]
        [(set! ,lhs (,binop ,[Triv -> x-live] ,[Triv -> y-live]))
          (add-conflicts! ct lhs live*)
          (set-cons x-live (set-cons y-live (remq lhs live*)))]
        [(set! ,lhs ,[Triv -> var])
          (add-conflicts! ct lhs live*)
          (let* ([new-live-set (remq lhs live*)])
            (if (null? var)
                new-live-set
                (set-cons var new-live-set)))]
        ;; Return the list of variables live in the tail ignoring the variables that were live before the call was made.
        [(return-point ,rplab ,tail) (Tail tail ct)])))
  (define Effect*
    (lambda (x live* ct)
      (match x
        [() live*]
        [(,ef* ... ,ef) (Effect* ef* (Effect ef live* ct) ct)])))
  (define Pred
    (lambda (x t-live* f-live* ct)
      (match x
        [(true) t-live*]
        [(false) f-live*]
        [(if ,test ,[c-live*] ,[a-live*])
          (union t-live* f-live* (Pred test c-live* a-live* ct))]
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(,predop ,[Triv -> x-live] ,[Triv -> y-live])
          (remove-nulls (union (list x-live) (list y-live) t-live* f-live*))])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))
          

;; pass: assign-registers
;; 1. If the list of variables is empty, return an empty list of register assignments.
;; 2. Pick a low-degree variable (either spillable or unspillable) from the list of variables, if one exists.
;;    Otherwise pick any spillable variable. A low-degree variable is one that conflicts with with fewer than
;;    k variables or registers in the current conflict table.
;; 3. Recur with the picked variable removed from the list of variables and the picked variable removed from
;;    the conflict lists of the other variables in the conflict table. (Thus, we expect the recursive call assign
;;    registers to a list one shorter with a conflict graph that possibly has fewer conflicts.) The recursive
;;    call should return a list of register assignments for (at least some of) the remaining variables.
;; 4. Attempt to select a register for the picked variable, avoiding any registers the picked variable conflicts
;;    with and any registers to which a conflicting variable is assigned in the list of register assignments
;;    returned by the recursive call. This step will succeed if a low-degree variable is picked, and may or
;;    may not succeed otherwise. If it succeeds, add the assignment to the list of register assignments and
;;    return the updated list. Otherwise return the non-updated list.
;; output:
#|
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locals (uvar*)
                (ulocals (uvar*)
                  (spills (uvar*)
                    (locate ([uvar fvar]*)
                      (frame-conflict conflict-graph Tail)))))
          |   (locate ([uvar Loc]*) Tail)
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Var Var Var)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
(define-who assign-registers
  (define replace
    (lambda (allocations conflict-uvars)
      (map (lambda (uvar)
             (let ([reg (assq uvar allocations)])
               (if (eq? reg #f) uvar (cadr reg))))
        (cdr conflict-uvars))))
  (define num-conflicts
    (lambda (var ct)
      (length (cdr (assq var ct)))))
  (define pick-min
    (lambda (var degree var* ct)
      (cond
        [(null? var*) var]
        [(<= degree (num-conflicts (car var*) ct)) (pick-min var degree (cdr var*) ct)]
        [else (let* ([node (car var*)]
                     [degree^ (num-conflicts node ct)])
                (pick-min node degree^ (cdr var*) ct))])))
  (define find-homes
    (lambda (var* var2* ct results)
      (cond
        [(and (null? var*) (null? var2*)) results]
        [(null? var*) (find-homes var2* '() ct results)]
        [else (let* ([current-var (pick-min (car var*) (num-conflicts (car var*) ct) (cdr var*) ct)]
                     [conflict-uvars (assq current-var ct)]
                     [conflict-entry (replace results conflict-uvars)]
                     [remaining-registers (difference registers conflict-entry)])
                (if (null? remaining-registers)
                    (find-homes (remq current-var var*) var2* ct results)
                    (let* ([assign-register (car remaining-registers)]
                           [results (cons (list current-var assign-register) results)])
                      (find-homes (remq current-var var*) var2* ct results))))])))
  (define Body
    (lambda (x)
      (match x
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (locate (,frame-home* ...)
               (frame-conflict ,fv-ct
                 (register-conflict ,ct ,tail)))))
          (let* ([uvar* (append local* ulocal*)]
                 [home* (find-homes local* ulocal* ct '())]
                 [spill* (difference uvar* (map car home*))])
            (cond
              [(null? spill*)
                `(locate (,frame-home* ... ,home* ...) ,tail)]
              ;; none of the frame locations should be spilled, 
              ;; because frame locations was artificially added
              [(null? (intersection ulocal* spill*))
                (let ([local* (difference local* spill*)])
                  `(locals ,local*
                    (ulocals ,ulocal*
                      (spills ,spill*
                        (locate ,frame-home*
                          (frame-conflict ,fv-ct ,tail))))))]
              [else
                (printf "::~s \n" home*)
                (errorf who "unspillable variables (~s) have been spilled"
                  (difference spill* local*))]))]
        [(locate (,home* ...) ,tail) `(locate ,home* ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; Checks to see if all variables have got a home, and basically decides wether compiler should go on with allocation or stop
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
;; spilled variables to frame home.
(define-who assign-frame
  (define remove-occurence
    (lambda (var ct)
      (map (lambda (x) 
             (cond
               [(eq? (car x) var) x]
               [else (remq var x)]))
        ct)))
  (define replace
    (lambda (allocations conflict-uvars)
      (map (lambda (uvar)
             (let ([reg (assq uvar allocations)])
               (if (eq? reg #f) uvar (cadr reg))))
        (cdr conflict-uvars))))
  (define find-homes
    (lambda (var* ct home*)
      (cond
        [(null? var*) home*]
        [else (let* ([current-var (car var*)]
                     [new-conflict-table (remove-occurence current-var ct)]
                     [results (find-homes (remq current-var var*) new-conflict-table home*)]
                     [conflict-uvars (assq current-var ct)]
                     [conflict-entry (replace results conflict-uvars)]
                     [assign-register (car (difference registers conflict-entry))]
                     [max-val (find-max (map (lambda (z) (if (frame-var? z)
                                                             (frame-var->index z)
                                                             '-1))
                                          conflict-entry))]
                     [assigned-frame (index->frame-var (add1 max-val))])
                (cons `(,current-var ,assigned-frame) results))])))
  (define Body
    (lambda (x)
      (match x
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,tail)))))
          (let ([home* (find-homes spill* ct home*)])
            `(locals ,local*
              (ulocals ,ulocal*
                (locate ,home*
                  (frame-conflict ,ct ,tail)))))]
        [(locate (,home* ...) ,tail) `(locate ,home* ,tail)]
        [,other (errorf who "invalid Body ~s" body)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; pass: discard-call-live
;; This pass discards the Loc* list included in each call. The grammar for the output of this pass is the
;; essentially same as the grammar for the source language of Assignment 3. The only difference is that
;; the locate form right-hand sides are registers rather than Locs (registers or frame variables). This minor
;; difference should not precipitate any changes to the that come after this one.
;; input:
#|
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locate ([uvar reg]*) Tail)
Tail    ----> (Triv Loc*)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Var Var Var)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
(define-who discard-call-live
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[live*])
          (make-begin `(,ef* ... ,live*))]
        [(if ,[Pred -> test] ,[conseq] ,[alt])
          `(if ,test ,conseq ,alt)]
        [(,target ,live* ...) `(,target)])))
  (define Pred
    (lambda (pr)
      (match pr
        [(if ,[test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[pr]) (make-begin `(,ef* ... ,pr))]
        ;; Pred    ----> (true)
        ;;           |   (false)
        ;;           |   (relop Triv Triv)
        [,other other])))
  (define Effect
    (lambda (ef)
      (match ef
        [(begin ,[ef*] ... ,[ef]) (make-begin `(,ef* ... ,ef))]
        [(if ,[Pred -> test] ,[conseq] ,[altern]) `(if ,test ,conseq ,altern)]
        [(return-point ,rplab ,[Tail -> tail]) `(return-point ,rplab ,tail)]
        ;; Effect  ----> (nop)
        ;;           |   (set! Var Triv)
        ;;           |   (set! Var (binop Triv Triv))
        ;;           |   (set! Var (mref Triv Triv))
        ;;           |   (mset! Var Var Var)
        [,other other])))
  (define Body
    (lambda (bd)
      (match bd
        [(locate ([,uvar* ,loc*] ...) ,[Tail -> tail])
          `(locate ([,uvar* ,loc*] ...) ,tail)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> bd*])] ...) ,[Body -> bd])
        `(letrec ([,label* (lambda () ,bd*)] ...) ,bd)])))


;; pass: finalize-locations
;; This pass replaces each occurrence of a uvar in the body of each locate form with the corresponding Loc.
;; It also discards the locate form.
;; input:
#|
Program ----> (letrec ([label (lambda () Body)]*) Body)
Body    ----> (locate ([uvar reg]*) Tail)
Tail    ----> (Triv)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Var Triv)
          |   (set! Var (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Var Var Var)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Var     ----> uvar | Loc
Triv    ----> Var | int | label
|#
(define-who finalize-locations
  (define Body
    (lambda (body)
      (match body
        [(locate ([,uvar* ,loc*] ...) ,tail)
          ((Tail (map cons uvar* loc*)) tail)])))
  (define Tail
    (lambda (env)
      (lambda (tail)
        (match tail
          [(if ,[(Pred env) -> pred] ,[tail-a] ,[tail-b])
            `(if ,pred ,tail-a ,tail-b)]
          [(begin ,[(Effect env) -> effect*] ... ,[tail])
            (make-begin `(,effect* ... ,tail))]
          [(,[(Triv env) -> triv]) `(,triv)]))))
  (define Pred
    (lambda (env)
      (lambda (pred)
        (match pred
          [(true) '(true)]
          [(false) '(false)]
          [(begin ,[(Effect env) -> effect*] ... ,[pred])
            (make-begin `(,effect* ... ,pred))]
          [(if ,[pred-a] ,[pred-b] ,[pred-c])
            `(if ,pred-a ,pred-b ,pred-c)]
          [(,relop ,[(Triv env) -> triv-a] ,[(Triv env) -> triv-b])
            `(,relop ,triv-a ,triv-b)]))))
  (define Effect
    (lambda (env)
      (lambda (effect)
        (match effect
          [(nop) '(nop)]
          ;; Effect  ----> (set! Var (binop Triv Triv))
          ;;           |   (set! Var (mref Triv Triv))
          [(set! ,[(Var env) -> var] (,binop ,[(Triv env) -> triv-a] ,[(Triv env) -> triv-b]))
            `(set! ,var (,binop ,triv-a ,triv-b))]
          [(set! ,[(Var env) -> var] ,[(Triv env) -> triv]) 
            (if (eq? var triv)
              '(nop)
              `(set! ,var ,triv))]
          [(mset! ,[(Var env) -> base] ,[(Var env) -> offset] ,[(Var env) -> val])
            `(mset! ,base ,offset ,val)]
          [(return-point ,rplab ,[(Tail env) -> tail])
           	`(return-point ,rplab ,tail)]
          [(if ,[(Pred env) -> pred] ,[ef-a] ,[ef-b])
            `(if ,pred ,ef-a ,ef-b)]
          [(begin ,[effect] ,[effect*] ... )
            (make-begin `(,effect ,effect* ...))]))))
  (define Triv
    (lambda (env)
      (lambda (triv)
        (if (or (integer? triv)
                (label? triv))
            triv
            ((Var env) triv)))))
  (define Var
    (lambda (env)
      (lambda (var)
        (if (uvar? var)
            (cdr (assq var env))
            var))))
  (lambda (program)
    (match program 
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body]) 
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)])))


;; pass: expose-frame-var
;; The job of expose-frame-var is to convert occurrences of the frame variables fv0, fv1, etc., into
;; displacement mode operands (see the X86_64 Primer), with frame-pointer-register as the base register and an offset based on
;; the frame variable's index. Since our words are 64 bits, i.e., 8 bytes, the offset for fvi should be 8i, e.g., 0,
;; 8, 16, etc., for fv0, fv1, fv2, etc.
;; (mset! x y z) means x[y] = z
;; if x is assigned a register and y a int then I make a displacement operand
;; if x and y are assigned registers then I make an index operands
;; otherwise I simply swap x and y and make a displacement operand ditto while handling the mrefs 
;; input:
#|
Program ----> (letrec ([label (lambda () Tail)]*) Tail)
Tail    ----> (Triv)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Loc Triv)
          |   (set! Loc (binop Triv Triv))
          |   (set! Var (mref Triv Triv))
          |   (mset! Var Var Var)
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | fvar
Triv    ----> Loc | int | label
|#
(define-who expose-frame-var
  (define Pred
    (lambda (fp-offset)
      (lambda (pred)
        (match pred
          [(begin ,ef* ... ,pr)
            (let*-values ([(ef* fp-offset) ((Effect* fp-offset) ef*)]
                          [(pr fp-offset) ((Pred fp-offset) pr)])
              (values (make-begin `(,ef* ... ,pr)) fp-offset))]
          [(if ,[(Pred fp-offset) -> test fp-offset] ,conseq ,alt)
            (let-values ([(conseq c-offset) ((Pred fp-offset) conseq)]
                         [(alt a-offset) ((Pred fp-offset) alt)])
              (values `(if ,test ,conseq ,alt) fp-offset))]
          [(,relop ,[(Triv fp-offset) -> tr1] ,[(Triv fp-offset) -> tr2])
            (values `(,relop ,tr1 ,tr2) fp-offset)]
          ;; Pred    ----> (true)
          ;;           |   (false)
          [,other (values other fp-offset)]))))
  (define Effect
    (lambda (fp-offset)
      (lambda (ef)
        (match ef
          [(set! ,fp (+ ,fp ,n)) (guard (eq? fp frame-pointer-register))
            (values ef (+ fp-offset n))]
          [(set! ,fp (- ,fp ,n)) (guard (eq? fp frame-pointer-register))
            (values ef (- fp-offset n))]
          [(set! ,[(Triv fp-offset) -> var] (mref ,[(Triv fp-offset) -> t1] ,[(Triv fp-offset) -> t2]))
            (cond
              [(and (register? t1) (register? t2))
                (values `(set! ,var ,(make-index-opnd t1 t2)) fp-offset)]
              [(and (register? t1) (int32? t2))
                (values `(set! ,var ,(make-disp-opnd t1 t2)) fp-offset)]
              [(and (int32? t1) (register? t2))
                (values `(set! ,var ,(make-disp-opnd t2 t1)) fp-offset)])]
          [(set! ,[(Triv fp-offset) -> var] (,binop ,[(Triv fp-offset) -> t1] ,[(Triv fp-offset) -> t2]))
            (values `(set! ,var (,binop ,t1 ,t2)) fp-offset)]
          [(set! ,[(Triv fp-offset) -> var] ,[(Triv fp-offset) -> t])
            (values `(set! ,var ,t) fp-offset)]
          [(mset! ,[(Triv fp-offset) -> base] ,[(Triv fp-offset) -> offset] ,[(Triv fp-offset) -> value])
            (cond
              [(and (int32? base) (register? offset))
                (values `(set! ,(make-disp-opnd offset base) ,value) fp-offset)]
              [(and (register? base) (int32? offset))
                (values `(set! ,(make-disp-opnd base offset) ,value) fp-offset)]
              [else (values `(set! ,(make-index-opnd base offset) ,value) fp-offset)])]
          [(begin ,ef* ... ,ef)
            (let*-values ([(ef* fp-offset) ((Effect* fp-offset) ef*)]
                          [(ef fp-offset) ((Effect fp-offset) ef)])
              (values (make-begin `(,ef* ... ,ef)) fp-offset))]
          [(if ,[(Pred fp-offset) -> test fp-offset] ,conseq ,alt)
            (let-values ([(conseq c-offset) ((Effect fp-offset) conseq)]
                         [(alt a-offset) ((Effect fp-offset) alt)])
              (values `(if ,test ,conseq ,alt) fp-offset))]
          [(return-point ,rplab ,[(Tail fp-offset) -> tail fp-offset])
            (values `(return-point ,rplab ,tail) fp-offset)]
          ;; Effect  ----> (nop)
          [,other (values other fp-offset)]))))
  (define Effect*
    (lambda (fp-offset)
      (lambda (ef*)
        (if (null? ef*)
            (values '() fp-offset)
            (let-values ([(ef fp-offset) ((Effect fp-offset) (car ef*))])
              (let-values ([(ef* fp-offset) ((Effect* fp-offset) (cdr ef*))])
                (values (cons ef ef*) fp-offset)))))))
  (define Triv
    (lambda (fp-offset)
      (lambda (t)
        (if (frame-var? t)
            (make-disp-opnd frame-pointer-register 
              (- (ash (frame-var->index t) align-shift) fp-offset))
            t))))
  (define Tail
    (lambda (fp-offset)
      (lambda (tail)
        (match tail
          [(begin ,ef* ... ,tail)
            (let*-values ([(ef* fp-offset) ((Effect* fp-offset) ef*)]
                          [(tail fp-offset) ((Tail fp-offset) tail)])
              (values (make-begin `(,ef* ... ,tail)) fp-offset))]
          [(if ,[(Pred fp-offset) -> test fp-offset] ,conseq ,alt)
            (let-values ([(conseq c-offset) ((Tail fp-offset) conseq)]
                         [(alt a-offset) ((Tail fp-offset) alt)])
              (values `(if ,test ,conseq ,alt) fp-offset))]
          [(,[(Triv fp-offset) -> t])
            (values `(,t) fp-offset)]))))
  (define Body
    (lambda (x)
      (let-values ([(x fp-offset) ((Tail 0) x)])
        (unless (= fp-offset 0)
          (errorf who "nonzero final fp-offset ~s" fp-offset))
        x)))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> tail*])] ...) ,[Body -> tail])
        `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)])))


;; pass: expose-basic-blocks
;; This creates a new letrec binding for dealing with consequent and alternative parts of an if-expression 
;; so that the next pass can produce jumps more easily. We create a new binding for consequent and 
;; alternative at every stage we go on appending any new bindings created to a list and keep passing that list
;; Processing goes in a bottom up manner.
;; input:
#|
Program ----> (letrec ([label (lambda () Tail)]*) Tail)
Tail    ----> (Triv)
          |   (if Pred Tail Tail)
          |   (begin Effect* Tail)
Pred    ----> (true)
          |   (false)
          |   (relop Triv Triv)
          |   (if Pred Pred Pred)
          |   (begin Effect* Pred)
Effect  ----> (nop)
          |   (set! Loc Triv)
          |   (set! Loc (binop Triv Triv))
          |   (return-point label Tail)
          |   (if Pred Effect Effect)
          |   (begin Effect* Effect)
Loc     ----> reg | #<disp reg offset> | #<index breg ireg>
Triv    ----> Loc | int | label
|#
(define-who expose-basic-blocks
  (define new-def* '())
  (define add-def
    (lambda (label body)
      (set! new-def* (cons `[,label (lambda () ,body)] new-def*))))
  (define Tail
    (lambda (x)
      (match x
        ;; Tail    ----> (if Pred Tail Tail)
        [(if ,t ,[c] ,[a])
          (let ([cl (unique-label 'c)] [al (unique-label 'a)])
            (add-def cl c) (add-def al a)
            (Pred t cl al))]
        ;; Tail    ----> (begin Effect* Tail)
        [(begin ,ef* ... ,[tail])
          (Effect* ef* `(,tail))]
        ;; Tail    ----> (Triv)
        [,other other])))
  (define Pred
    (lambda (x t f)
      (match x
        ;; Pred    ----> (true)
        [(true) `(,t)]
        ;; Pred    ----> (false)
        [(false) `(,f)]
        ;; Pred    ----> (if Pred Pred Pred)
        [(if ,pr ,[conseq] ,[alt])
          (let ([cl (unique-label 'c)] [al (unique-label 'a)])
            (add-def cl conseq) (add-def al alt)
            (Pred pr cl al))]
        ;; Pred    ----> (begin Effect* Pred)
        [(begin ,ef* ... ,[pr])
          (Effect* ef* `(,pr))]
        ;; Pred    ----> (relop Triv Triv)
        [,other `(if ,other (,t) (,f))])))
  (define Effect*
    (lambda (x rest*)
      (match x
        [() (make-begin rest*)]
        [(,x* ... ,x) (Effect x* x rest*)])))
  (define Effect
    (lambda (bf* x af*)
      (match x
        ;; Effect  ----> (nop)
        [(nop) (Effect* bf* af*)]
        ;; Effect  ----> (begin Effect* Effect)
        [(begin ,ef* ... ,ef)
          (Effect (append bf* ef*) ef af*)]
        ;; Effect  ----> (return-point label Tail)
        [(return-point ,label ,[Tail -> tail])
          (add-def label (make-begin af*))
          (Effect* bf* `(,tail))]
        ;; Effect  ----> (if Pred Effect Effect)
        [(if ,t ,c ,a)
          (let* ([cl (unique-label 'c)]
                 [al (unique-label 'a)]
                 [jl (unique-label 'j)]
                 [c (Effect '() c `((,jl)))]
                 [a (Effect '() a `((,jl)))]
                 [t (Pred t cl al)])
            (add-def cl c) (add-def al a)
            (add-def jl (make-begin af*))
            (Effect* bf* `(,t)))]
        ;; Effect  ----> (set! Loc Triv)
        ;;           |   (set! Loc (binop Triv Triv))
        [,other (Effect* bf* (cons other af*))])))
  (lambda (x)
    (set! new-def* '())
    (match x
      ;; Program ----> (letrec ([label (lambda () Tail)]*) Tail)
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
        `(letrec (,new-def* ... [,label* (lambda () ,tail*)] ...) ,tail)])))


;; pass: flatten-program
;; This pass flattens out the now slightly nested structure of our source language into one that more closely
;; resembles assembly language, no letrec, no begin forms, calls turned into explicit jumps, and the names
;; of procedures turned into label forms. It produces a singlecodeform containing a sequence of labels, effect
;; expressions, and jumps, with the code for the body of the letrec appearing first followed by the body of
;; each lambda expression in turn, prefixed by its label.
;; (if cond (conseq) (alt)) =>
;; (if cond (jump conseq))
;; (jump alt)
;; or
;; (if (not cond) (jump alt))
;; (jump conseq)
;; input:
#|
Program ----> (letrec ([label (lambda () Tail)]*) Tail)
Tail    ----> (Triv)
          |   (if (relop Triv Triv) (,label) (,label))
          |   (begin Effect* Tail)
Effect  ----> (set! Loc Triv)
          |   (set! Loc (binop Triv Triv))
Loc     ----> reg | fvar
Triv    ----> Loc | int | label
|#
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
          (if (null? label*)
              `((if ,pred (jump ,conseq)) (jump ,alt))
              (let ([next-label (car label*)])
                (cond 
                  [(eq? next-label conseq)
                    `((if (not ,pred) (jump ,alt)))]
                  [(eq? next-label alt)
                    `((if ,pred (jump ,conseq)))]
                  [else
                    `((if ,pred (jump ,conseq)) (jump ,alt))])))]
        [(begin ,effect* ... ,tail)
          `(,effect* ... ,@(Tail label* tail))]
        [(,triv) `((jump ,triv))])))
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,tail*)] ...) ,tail)
        (let ([ev-tail (Tail label* tail)]
              [defn (make-body label* tail*)])
          `(code ,@ev-tail ,@defn))])))


;; This pass must be modified to handle the code form in place of the begin form (which is trivial) and to add
;; handling for labels, jumps, and the new operators logand, logor, and sra.
;; using the cmpq and conditional jump instructions je, jne, jl, jle, jg, and jge.
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
  (define Statement
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
  (define generatecode
    (lambda (program)
      (match program
        [(code ,stmt* ...) 
          (for-each Statement stmt*)])))
  (lambda (program)
    ;; (generatecode program) not be apply in advance 
    ;; because of emit-program is a customized syntax rather than a proceduce.
    (emit-program (generatecode program))))


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
