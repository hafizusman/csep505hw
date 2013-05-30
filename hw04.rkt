#lang plai-typed

(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)


(define-type Value 
  [numV (value : number)] ; A numeric value. 
  ; A function closure: 
  [funV (var : symbol) ; The name of the function's argument. 
        (body : Expr) ; The body of the function. 
        (env : Env)]
  [undefV (_ : void)]) ; The function's evaluation environment. 

(define (lookup [s : symbol] [env : Env]) : Value
  (if (empty? env)
      (error 'lookup (string-append "symbol not found: " (to-string s)))
      (if (symbol=? s (bind-name (first env)))
          (bind-val (first env))
          (lookup s (rest env)))))

(define-type Expr 
  [numE (value : number)] ; a numeric literal expression 
  [addE (lhs : Expr) 
        (rhs : Expr)] ; an addition expression
  [mulE (lhs : Expr) 
        (rhs : Expr)] ; a multiplication expression 
  [subE (lhs : Expr) 
        (rhs : Expr)] ; a subtraction expression 
  [varE (name : symbol)] ; A variable reference. 
  [funE (var : symbol) ; The name of the function arguments. 
        (body : Expr)] ; The body of the function. 
  [appE (fun : Expr) ; The function being applied. 
        (arg : Expr)]
  [withE (var : symbol) ; The variable being bound. 
         (bound : Expr) ; What the variable is being bound to. 
         (body : Expr)] ; The body in which the variable is bound. 
  [if0E (if-expr : Expr)
        (then-expr : Expr)
        (else-expr : Expr)]
  [recE (name : symbol)
        (value : Expr)])


(define (parse [s-exp : s-expression]) : Expr
  (cond 
    [(s-exp-number? s-exp) (numE (s-exp->number s-exp))]
    [(s-exp-symbol? s-exp) (varE (s-exp->symbol s-exp))]
    [(s-exp-list? s-exp) 
     (let ([lst (s-exp->list s-exp)]) 
       (cond 
         [(= 2 (length lst))
          (appE (parse (first lst)) 
                (parse (second lst)))]
         
         [(= 3 (length lst)) 
          (cond
            [(s-exp-symbol? (first lst))
             (case (s-exp->symbol (first lst)) 
               [(+) (addE (parse (second lst)) 
                          (parse (third lst)))] 
               [(*) (mulE (parse (second lst)) 
                          (parse (third lst)))]
               [(-) (subE (parse (second lst))
                          (parse (third lst)))]
               [(with) (withE (s-exp->symbol (first (s-exp->list (second lst))))
                              (parse (second (s-exp->list (second lst))))
                              (parse (third lst)))]
               [(fun) (funE (s-exp->symbol (first (s-exp->list (second lst)))) 
                            (parse (third lst)))]
               [(rec) (recE (s-exp->symbol (second lst))
                            (parse (third lst)))]
               [else (error 'parse (string-append 
                                    "unknown operator 3len " 
                                    (to-string (first lst))))])])]
         
         [(= 4 (length lst))
          (cond
            [(s-exp-symbol? (first lst))
             (case (s-exp->symbol (first lst))
               [(if0) (if0E (parse (second lst))
                            (parse (third lst))
                            (parse (fourth lst)))])])]
         [else (error 'parse (string-append "unknown number of args: " (to-string (length lst))))]))]
    [else (error 'parse (string-append "syntax error in " (to-string s-exp)))]))
 

(define (num+ [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (+ (numV-value l) (numV-value r)))
      (error 'num+ "num+ incorrect lhs and/or rhs type!!")))

(define (num* [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (* (numV-value l) (numV-value r)))
      (error 'num* "num* incorrect lhs and/or rhs type!!")))

(define (num- [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (- (numV-value l) (numV-value r)))
      (error 'num+ "num- incorrect lhs and/or rhs type!!")))


(define (interp [expr : Expr] 
                [env : Env]) : Value 
  (type-case Expr expr 
    [numE (value) 
          (numV value)]
    
    [addE (lhs rhs) 
          (num+ (interp lhs env) (interp rhs env))]
    
    [mulE (lhs rhs) 
          (num* (interp lhs env) (interp rhs env))] 

    [subE (lhs rhs) 
          (num- (interp lhs env) (interp rhs env))] 
    
    [varE (name)
          (lookup name env)] 
    
    [withE (var bound body) 
           (interp body 
                   (extend-env (bind var
                                     (interp bound env))
                               env))] 
    
    [funE (var body) 
          (funV var body env)] 

    [appE (f a) 
          (local ([define f-value (interp f env)])
                  (interp (funV-body f-value)
                          (extend-env (bind (funV-var f-value) 
                                            (interp a env))
                                      (funV-env f-value))))]

    #;[appE (fun arg)
          (let ([temp (extend-env
                       (funV-var (interp fun env)) 
                       (interp arg env) 
                       env)])
            (interp (funV-body (interp fun temp)) temp))]

    [if0E (i t e) (if (= 0 (numV-value (interp i env)))
                      (interp t env)
                      (interp e env))]
    
    [recE (name value) 
          (error 'todo "TODO\n")
          #;(interp value env)
          #;(let* ([b (box (undefV (void)))]
                              [bound-val (interp value 
                                                 (extend-env name
                                                             b
                                                             env))])
                         (begin
                           (set-box! b bound-val)
                           (numV 1234)))
          ]))


; A 'with' expression binds a value to a variable within its body. 
(define test-with-expr 
  '(with (x (+ 1 2)) 
         (* x 3))) ; => 9 

; A 'with' expression binds a value to a variable within its body. 
(define test-with-expr-2
  '(with (x (- 2 1)) 
         (* x 3))) ; => 3 

; A 'fun' (function) abstracts a body over a variable. 
(define test-funD-expr 
  '(fun (x) (+ x 5))) ; A function that adds 5 to its argument. 

; Functions have access to variable bindings in the enclosing (lexical) scope. 
(define test-funDwithBinding-expr 
  '(with (y (+ 3 4)) 
         (fun (x) (* x y)))) ; A function that multiplies its argument by 7. 

; Applying a function to a value. 
(define test-funA-expr 
  '((fun (x) (* x x)) 
    5)) ; => 25 
; Applying a function to a value. 
(define test-funA-expr-2
  '((fun (x) (* x x)) 
    y)) ; => y 

; Example combining 'with', 'fun', and application. 
(define test-funwith-expr 
  '(with (y 3) 
         (with (f (fun (x) (* x y)))
               (+ (f 8) (f (f 2)))))) ; => 42 

(define test-rec-expr
  '(rec fact 
     (fun (n) 
          (if0 n 
               1 
               (* n (fact (- n 1)))))))

(define test-rec-app-expr
  '((rec fact 
     (fun (n) 
          (if0 n 
               1 
               (* n (fact (- n 1))))))
    (fact 3)))


(test (interp (parse test-with-expr) empty-env) (numV 9))
(test (interp (parse test-with-expr-2) empty-env) (numV 3))
(test (interp (parse test-funA-expr) empty-env) (numV 25))
(test/exn (interp (parse test-funA-expr-2) empty-env) "lookup: symbol not found: 'y")
(test (interp (parse test-funwith-expr) empty-env) (numV 42))
(test (interp (parse '(* 3 (if0 (+ 1 2) 5 (* 3 4)))) empty-env) (numV 36)) 
(test (interp (parse '(if0 (* 1 0) 5 (* 3 4))) empty-env) (numV 5)) 
(test (interp (parse test-rec-expr) empty-env) (numV 4))
