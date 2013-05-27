;;;
;;; Chapter 9
;;;

;; 9.2 Recursive Functions



;; Exercise
;; Run the equivalent program through your interpreter for boxes and make sure it produces a cyclic value. How do you check this?

; To implement recursive functions: first create a placeholder, then refer to the placeholder where we want the cyclic reference, and finally mutate the placeholder before use
; To implement recursive data: first name an vacant placeholder; then mutate the placeholder so its content is itself; to obtain “itself”, use the name previously bound. Of course, we need not be limited to “self-cycles”: we can also have mutually-cyclic data (where no one element is cyclic but their combination is).
#lang plai-typed

(define-type ExprC
  [numC (n : number)] 
  [idC (s : symbol)] 
  [appC (fun : ExprC) (arg : ExprC)] 
  [plusC (l : ExprC) (r : ExprC)] 
  [multC (l : ExprC) (r : ExprC)] 
  [lamC (arg : symbol) (body : ExprC)] 
  [boxC (arg : ExprC)] 
  [unboxC (arg : ExprC)] 
  [setboxC (b : ExprC) (v : ExprC)] 
  [seqC (b1 : ExprC) (b2 : ExprC)]
  [if0C (i : ExprC) (t : ExprC) (e : ExprC)]) 

(define-type-alias Location number)

(define-type Binding
  [bind (name : symbol) (val : Location)])
(define-type-alias Env (listof Binding))
(define empty-env empty)
(define extend-env cons)

(define-type Storage
  [cell (location : Location) (val : Value)])
(define-type-alias Store (listof Storage))
(define empty-store empty)
(define override-store cons)

(define-type Value
  [numV (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [boxV (l : Location)])

(define-type Result
  [v*s (v : Value) (s : Store)])


(define new-loc
  (let ([n (box 0)])
    (λ ()
      (begin
        (set-box! n (add1 (unbox n)))
        (unbox n)))))

(define (lookup [s : symbol] [env : Env]) : Location
  (if (empty? env)
      (error 'lookup (string-append "symbol not found: " (to-string s)))
      (if (symbol=? s (bind-name (first env)))
          (bind-val (first env))
          (lookup s (rest env)))))

(define (fetch [loc : Location] [sto : Store]) : Value
  (if (empty? sto)
      (error 'fetch (string-append "loc not found: " (to-string loc)))
      (if (= loc (cell-location (first sto)))
          (cell-val (first sto))
          (fetch loc (rest sto)))))

(define (num+ [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (+ (numV-n l) (numV-n r)))
      (error 'num+ "num+ incorrect lhs and rhs type!!")))

(define (num* [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (* (numV-n l) (numV-n r)))
      (error 'num* "num* incorrect lhs and rhs type!!")))


(define (interp [expr : ExprC] [env : Env] [sto : Store]) : Result
  (type-case ExprC expr 
    [numC (n) (v*s 
               (numV n) 
               sto)] 
    
    [idC (n) (v*s 
              (fetch 
               (lookup n env) 
               sto) 
              sto)] 
    
    [appC (f a) (type-case Result (interp f env sto)
                  [v*s (v-f s-f)
                       (type-case Result (interp a env s-f)
                         [v*s (v-a s-a)
                              (let ([where (new-loc)]) 
                                (interp (closV-body v-f) 
                                        (extend-env (bind (closV-arg v-f) 
                                                          where) 
                                                    (closV-env v-f)) 
                                        (override-store (cell where v-a) s-a)))])])]
    
    [plusC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r)
                               (v*s (num+ v-l v-r) s-r)])])] 
    
    [multC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r) 
                               (v*s (num* v-l v-r) s-r)])])] 
    
    [lamC (a b) (v*s 
                 (closV a b env) 
                 sto)]
    
    [boxC (a) (type-case Result (interp a env sto) 
                [v*s (v-a s-a) 
                     (let ([where (new-loc)]) 
                       (v*s (boxV where) 
                            (override-store (cell where v-a) 
                                            s-a)))])] 
    
    [unboxC (a) (type-case Result (interp a env sto) 
                  [v*s (v-a s-a) 
                       (v*s (fetch (boxV-l v-a) s-a) s-a)])] 
    
    [setboxC (b v) (type-case Result (interp b env sto) 
                     [v*s (v-b s-b) 
                          (type-case Result (interp v env s-b) 
                            [v*s (v-v s-v) 
                                 (v*s v-v 
                                      (override-store (cell (boxV-l v-b) 
                                                            v-v) 
                                                      s-v))])])] 
    
    [seqC (b1 b2) (type-case Result (interp b1 env sto)
                    [v*s (v-b1 s-b1)
                         (interp b2 env s-b1)])]
    
    [if0C (i t e) (type-case Result (interp i env sto)
                    [v*s (v-i s-i)
                         (if (= (numV-n v-i) 0)
                             (interp t env s-i)
                             (interp e env s-i))])]))

#;((λ (x)
   (begin
     (set-box! x x)
     x))
 (box 'dummy))


; will fail with error: fact: unbound identifier in module in: fact
#;(let ([fact (lambda (n) 
              (if 1 
                  n 
                  (* n (fact (- n 1)))))]) 
  (fact 10)) 

; above desugared with same error as above: fact: unbound identifier in module in: fact
#;((λ (fact)
   (lambda (n) 
              (if 1 
                  n 
                  (* n (fact (- n 1))))))
 (fact 10))


(define test-if0-true (if0C (numC 3) (numC 10) (numC 299)))
(define test-if0-false (if0C (numC 0) (numC 19) (numC 299)))

(test (interp test-if0-true empty-env empty-store) (v*s (numV 299) empty-store))
(test (interp test-if0-true empty-env empty-store) (v*s (numV 19) empty-store))

(define test-cyclic-data (appC (lamC 'x (seqC (setboxC (idC 'x) (idC 'x)) (idC 'x))) (boxC (numC 123))))


(define t (interp test-cyclic-data empty-env empty-store))

; todo: is this actually cyclic??
(test t (v*s (boxV 1) (list (cell 1 (boxV 1)) (cell 2 (boxV 1)) (cell 1 (numV 123)))))

;; compile following with plai
;#lang plai
;
;(let ([fact (box 'dummy)])
;  (let ([fact-fun
;         (λ (n)
;           (if (zero? n)
;               1
;               (* n ((unbox fact) (- n 1)))))])
;  (begin
;    (set-box! fact fact-fun)
;    ((unbox fact) 3))))
;
;; Desugaring above
;(let ([fact (box 'dummy)]) 
;  (begin 
;    (set-box! fact 
;              (lambda (n) 
;                (if (zero? n) 
;                    1 
;                    (* n ((unbox fact) (- n 1)))))) 
;    ((unbox fact) 10))) 
;
;
;; Using variables instead of boxes from above
;(let ([fact 'dummy]) 
;    (begin 
;      (set! fact 
;            (lambda (n) 
;              (if (zero? n) 
;                  1 
;                  (* n (fact (- n 1)))))) 
;      (fact 10))) 




; #lang plai
;
;; When the following program is Run, Racket prints this as: #0=’#&#0#. 
;; This notation is in fact precisely what we want. 
;; Recall that #& is how Racket prints boxes. 
;; The #0= (and similarly for other numbers) is how Racket names pieces of cyclic data. 
;; Thus, Racket is saying, “#0 is bound to a box whose content is #0#, i.e., 
;;  whatever is bound to #0, i.e., itself”.
;(let ([b (box 'dummy)])
;  (begin 
;    (set-box! b b)
;    b))
;
;
;
;;;
;#lang plai-typed
;
;(define-type ExprC
;  [numC (n : number)] 
;  [varC (s : symbol)] 
;  [appC (fun : ExprC) (arg : ExprC)] 
;  [plusC (l : ExprC) (r : ExprC)] 
;  [multC (l : ExprC) (r : ExprC)] 
;  [lamC (arg : symbol) (body : ExprC)] 
;  [setC (var : symbol) (arg : ExprC)] 
;  [seqC (b1 : ExprC) (b2 : ExprC)]
;  [treeC (val : 'a) (left : ExprC) (right : ExprC)]
;  [listC (val : 'a) (next : ExprC)])
;
;(define my-list (listC 1 (listC 3 (listC 5 (listC 6 (numC 0))))))
;(define node1 (treeC 'abc (numC 0) (numC 0)))
;(define node2 (treeC 'xyz (numC 0) (numC 0)))
;(define node3 (treeC 'def node1 node2))
;(define my-tree (treeC 'uvw node3 (treeC '_ (numC 0) (numC 0))))
;
;my-list
;my-tree
;
;; won't work since b is undefined
;#;(let ([b b])
;  b)
;; the above desugared
;#;((λ (b)
;  b)
; b)
;; or even
;#;((λ (x)
;   x)
; b)
;
;;we need to first create a “place” for the datum, then refer to that place within itself. The use of “then”—i.e., the introduction of time—should suggest a mutation operation.
;;Note that this program will not run in Typed PLAI as written. We’ll return to typing such programs later [REF]. For now, run it in the untyped (#lang plai) language.;(let ([b (box 'dummy)])
;(let ([b (box 'dummy)])
;  (begin 
;    (set-box! b b)
;    b))
;


;;;;
;;;; Chapter 8
;;;;
;
;#lang plai-typed
;
;;; using variables (i.e. variable mutation )
;(define-type ExprC
;  [numC (n : number)] 
;  [varC (s : symbol)] 
;  [appC (fun : ExprC) (arg : ExprC)] 
;  [plusC (l : ExprC) (r : ExprC)] 
;  [multC (l : ExprC) (r : ExprC)] 
;  [lamC (arg : symbol) (body : ExprC)] 
;  [setC (var : symbol) (arg : ExprC)] 
;  [seqC (b1 : ExprC) (b2 : ExprC)]) 
;
;(define-type Value
;  [numV (n : number)]
;  [closV (arg : symbol) (body : ExprC) (env : Env)])
;
;(define-type-alias Location number)
;
;(define-type Binding
;  [bind (name : symbol) (val : Location)])
;(define-type-alias Env (listof Binding))
;(define empty-env empty)
;(define extend-env cons)
;
;(define-type Storage
;  [cell (location : Location) (val : Value)])
;(define-type-alias Store (listof Storage))
;(define empty-store empty)
;(define override-store cons)
;
;(define-type Result
;  [v*s (v : Value) (s : Store)])
;
;
;(define new-loc
;  (let ([n (box 0)])
;    (λ ()
;      (begin
;        (set-box! n (add1 (unbox n)))
;        (unbox n)))))
;
;(define (lookup [s : symbol] [env : Env]) : Location
;  (if (empty? env)
;      (error 'lookup (string-append "symbol not found: " (to-string s)))
;      (if (symbol=? s (bind-name (first env)))
;          (bind-val (first env))
;          (lookup s (rest env)))))
;
;(define (fetch [loc : Location] [sto : Store]) : Value
;  (if (empty? sto)
;      (error 'fetch (string-append "loc not found: " (to-string loc)))
;      (if (= loc (cell-location (first sto)))
;          (cell-val (first sto))
;          (fetch loc (rest sto)))))
;
;(define (num+ [l : Value] [r : Value]) : Value
;  (if (and (numV? l) (numV? r))
;      (numV (+ (numV-n l) (numV-n r)))
;      (error 'num+ "num+ incorrect lhs and rhs type!!")))
;
;(define (num* [l : Value] [r : Value]) : Value
;  (if (and (numV? l) (numV? r))
;      (numV (* (numV-n l) (numV-n r)))
;      (error 'num* "num* incorrect lhs and rhs type!!")))
;
;(define (interp [expr : ExprC] [env : Env] [sto : Store]) : Result
;  (type-case ExprC expr 
;    [numC (n) (v*s 
;               (numV n) 
;               sto)] 
;    
;    [varC (n) (v*s 
;               (fetch 
;                (lookup n env) 
;                sto) 
;               sto)] 
;    
;    [appC (f a) (type-case Result (interp f env sto)
;                  [v*s (v-f s-f)
;                       (type-case Result (interp a env s-f)
;                         [v*s (v-a s-a)
;                              (let ([where (new-loc)]) 
;                                (interp (closV-body v-f) 
;                                        (extend-env (bind (closV-arg v-f) 
;                                                          where) 
;                                                    (closV-env v-f)) 
;                                        (override-store (cell where v-a) s-a)))])])]
;    
;    [plusC (l r) (type-case Result (interp l env sto)
;                   [v*s (v-l s-l)
;                        (type-case Result (interp r env s-l)
;                          [v*s (v-r s-r)
;                               (v*s (num+ v-l v-r) s-r)])])] 
;    
;    [multC (l r) (type-case Result (interp l env sto)
;                   [v*s (v-l s-l)
;                        (type-case Result (interp r env s-l)
;                          [v*s (v-r s-r) 
;                               (v*s (num* v-l v-r) s-r)])])] 
;    
;    [lamC (a b) (v*s 
;                 (closV a b env) 
;                 sto)]
;    
;    [setC (var val) (type-case Result (interp val env sto)
;                      [v*s (v-val s-val)
;                           (let ([where (lookup var env)])
;                             (v*s v-val
;                                  (override-store 
;                                   (cell where v-val)
;                                   s-val)))])]
;    
;    [seqC (b1 b2) (type-case Result (interp b1 env sto)
;                    [v*s (v-b1 s-b1)
;                         (interp b2 env s-b1)])]
;    
;    ))
;
;(test (interp (appC
;           (lamC 
;           'x 
;           (plusC (setC 'x (numC 10)) (numC 100))) 
;           (numC 50))
;          empty-env 
;          empty-store)
;      (v*s (numV 110) (list (cell 1 (numV 10)) (cell 1 (numV 50)))))
;
;;; using identifiers (i.e. structure mutation )
;(define-type ExprC
;  [numC (n : number)] 
;  [idC (s : symbol)] 
;  [appC (fun : ExprC) (arg : ExprC)] 
;  [plusC (l : ExprC) (r : ExprC)] 
;  [multC (l : ExprC) (r : ExprC)] 
;  [lamC (arg : symbol) (body : ExprC)] 
;  [boxC (arg : ExprC)] 
;  [unboxC (arg : ExprC)] 
;  [setboxC (b : ExprC) (v : ExprC)] 
;  [seqC (b1 : ExprC) (b2 : ExprC)]) 
;
;(define-type-alias Location number)
;
;(define-type Binding
;  [bind (name : symbol) (val : Location)])
;(define-type-alias Env (listof Binding))
;(define empty-env empty)
;(define extend-env cons)
;
;(define-type Storage
;  [cell (location : Location) (val : Value)])
;(define-type-alias Store (listof Storage))
;(define empty-store empty)
;(define override-store cons)
;
;(define-type Value
;  [numV (n : number)]
;  [closV (arg : symbol) (body : ExprC) (env : Env)]
;  [boxV (l : Location)])
;
;(define-type Result
;  [v*s (v : Value) (s : Store)])
;
;
;(define new-loc
;  (let ([n (box 0)])
;    (λ ()
;      (begin
;        (set-box! n (add1 (unbox n)))
;        (unbox n)))))
;
;(define (lookup [s : symbol] [env : Env]) : Location
;  (if (empty? env)
;      (error 'lookup (string-append "symbol not found: " (to-string s)))
;      (if (symbol=? s (bind-name (first env)))
;          (bind-val (first env))
;          (lookup s (rest env)))))
;
;(define (fetch [loc : Location] [sto : Store]) : Value
;  (if (empty? sto)
;      (error 'fetch (string-append "loc not found: " (to-string loc)))
;      (if (= loc (cell-location (first sto)))
;          (cell-val (first sto))
;          (fetch loc (rest sto)))))
;
;(define (num+ [l : Value] [r : Value]) : Value
;  (if (and (numV? l) (numV? r))
;      (numV (+ (numV-n l) (numV-n r)))
;      (error 'num+ "num+ incorrect lhs and rhs type!!")))
;
;(define (num* [l : Value] [r : Value]) : Value
;  (if (and (numV? l) (numV? r))
;      (numV (* (numV-n l) (numV-n r)))
;      (error 'num* "num* incorrect lhs and rhs type!!")))
;
;
;(define (interp [expr : ExprC] [env : Env] [sto : Store]) : Result
;  (type-case ExprC expr 
;    [numC (n) (v*s 
;               (numV n) 
;               sto)] 
;    
;    [idC (n) (v*s 
;              (fetch 
;               (lookup n env) 
;               sto) 
;              sto)] 
;    
;    [appC (f a) (type-case Result (interp f env sto)
;                  [v*s (v-f s-f)
;                       (type-case Result (interp a env s-f)
;                         [v*s (v-a s-a)
;                              (let ([where (new-loc)]) 
;                                (interp (closV-body v-f) 
;                                        (extend-env (bind (closV-arg v-f) 
;                                                          where) 
;                                                    (closV-env v-f)) 
;                                        (override-store (cell where v-a) s-a)))])])]
;    
;    [plusC (l r) (type-case Result (interp l env sto)
;                   [v*s (v-l s-l)
;                        (type-case Result (interp r env s-l)
;                          [v*s (v-r s-r)
;                               (v*s (num+ v-l v-r) s-r)])])] 
;    
;    [multC (l r) (type-case Result (interp l env sto)
;                   [v*s (v-l s-l)
;                        (type-case Result (interp r env s-l)
;                          [v*s (v-r s-r) 
;                               (v*s (num* v-l v-r) s-r)])])] 
;    
;    [lamC (a b) (v*s 
;                 (closV a b env) 
;                 sto)]
;    
;    [boxC (a) (type-case Result (interp a env sto) 
;                [v*s (v-a s-a) 
;                     (let ([where (new-loc)]) 
;                       (v*s (boxV where) 
;                            (override-store (cell where v-a) 
;                                            s-a)))])] 
;    
;    [unboxC (a) (type-case Result (interp a env sto) 
;                  [v*s (v-a s-a) 
;                       (v*s (fetch (boxV-l v-a) s-a) s-a)])] 
;    
;    [setboxC (b v) (type-case Result (interp b env sto) 
;                     [v*s (v-b s-b) 
;                          (type-case Result (interp v env s-b) 
;                            [v*s (v-v s-v) 
;                                 (v*s v-v 
;                                      (override-store (cell (boxV-l v-b) 
;                                                            v-v) 
;                                                      s-v))])])] 
;    
;    [seqC (b1 b2) (type-case Result (interp b1 env sto)
;                    [v*s (v-b1 s-b1)
;                         (interp b2 env s-b1)])]
;    
;    ))
;
;; todo: Define begin by desugaring into let (and hence into lambda).
;; todo: Implement the other version of store alteration, whereby we update an existing binding and thereby avoid multiple bindings for a location in the store.
;; todo: It’s a useful exercise to try to limit the use of store locations only to boxes. How many changes would you need to make?
;; todo: Go through the interpreter; replace every reference to an updated store with a reference to one before update; make sure your test cases catch all the introduced errors!
;; todo: Augment the language with the journal features of software transactional memory journal.
;; todo: An alternate implementation strategy is to have the environment map names to boxed Values. We don’t do it here because it: (a) would be cheating, (b) wouldn’t tell us how to implement the same feature in a language without boxes, (c) doesn’t necessarily carry over to other mutation operations, and (d) most of all, doesn’t really give us insight into what is happening here. It is nevertheless useful to understand, not least because you may find it a useful strategy to adopt when implementing your own language. Therefore, alter the implementation to obey this strategy. Do you still need store-passing style? Why or why not?
;
;
;(define test1 (plusC (unboxC (boxC (numC 10))) (numC 9)))
;(define test2-seqC-take1 (seqC (plusC (numC 1) (numC 2)) (boxC (numC 100))))
;(define test3-seqC-take1 (seqC (boxC (numC 100)) (plusC (numC 1) (numC 2))))
;(define test4-seqC-take2 (seqC (plusC (numC 1) (numC 2)) (multC (numC 100) (numC 3))))
;(define test5-seqC-take2 (seqC (multC (numC 100) (numC 3)) (plusC (numC 1) (numC 2))))
;
;(test (interp test1 empty-env empty-store) (v*s (numV 19) (list (cell 1 (numV 10)))))
;(test (interp test2-seqC-take1 empty-env empty-store) (v*s (boxV 2) (list (cell 2 (numV 100)))))
;(test (interp test3-seqC-take1 empty-env empty-store) (v*s (numV 3) (list (cell 3 (numV 100)))))
;(test (interp test4-seqC-take2 empty-env empty-store) (v*s (numV 300) empty-store))
;(test (interp test5-seqC-take2 empty-env empty-store) (v*s (numV 3) empty-store))

;;;;
;;;; Chapter 7
;;;;
;
;
;(define-type ExprC
;  [numC (n : number)]
;  [idC (s : symbol)]
;  [appC (f : ExprC) (a : ExprC)]
;  [plusC (l : ExprC) (r : ExprC)]
;  [multC (l : ExprC) (r : ExprC)]
;  ;[fdC (f : symbol) (a : symbol) (b : ExprC)] ;A function is inherently anonymous, and we should separate its definition from its naming
;  [lamC (a : symbol) (b : ExprC)])
;
;(define-type Value
;  [numV (n : number)]
;  ;[funV (name : symbol) (arg : symbol) (body : ExprC)] ; We need to change our representation of values to record closures rather than raw function text
;  [closV (arg : symbol) (body : ExprC) (env : Env)]); a closure
;
;(define-type Binding
;  [bind (name : symbol) (val : Value)])
;
;(define-type-alias Env (listof Binding))
;(define empty-env empty)
;(define extend-env cons)
;
;(define (lookup [s : symbol] [env : Env]) : Value
;  (if (empty? env)
;      (error 'lookup (string-append "symbol not found: " (to-string s)))
;      (if (equal? s (bind-name (first env)))
;          (bind-val (first env))
;          (lookup s (rest env)))))
;
;(define (num+ [l : Value] [r : Value]): Value
;  (if (and (numV? l) (numV? r))
;      (numV (+ (numV-n l) (numV-n r)))
;      (error 'num+ "l and/or r are not numV's")))
;
;(define (num* [l : Value] [r : Value]): Value
;  (if (and (numV? l) (numV? r))
;      (numV (* (numV-n l) (numV-n r)))
;      (error 'num* "l and/or r are not numV's")))
;
;(define (interp [e : ExprC] [env : Env]) : Value
;  (type-case ExprC e
;    [numC (n) (numV n)]
;    [idC (s) (lookup s env)]
;    #;[appC (f a) (local ([define fd (interp f env)])
;                    (interp (funV-body fd) ;A function is inherently anonymous, and we should separate its definition from its naming
;                            (extend-env 
;                             (bind 
;                              (funV-arg fd) 
;                              (interp a env)) 
;                             empty-env)))]
;    [appC (f a) (local ([define f-value (interp f env)])
;                  (interp 
;                   (closV-body f-value)
;                   (extend-env 
;                    (bind 
;                     (closV-arg f-value) 
;                     (interp a env))
;                    (closV-env f-value))))]
;    [plusC (l r) (num+ (interp l env) (interp r env))]
;    [multC (l r) (num* (interp l env) (interp r env))]
;    ;[fdC (f a b) (funV f a b)] ;A function is inherently anonymous, and we should separate its definition from its naming
;    [lamC (a b) (closV a b env)]))
;
;;; use with without closV and lamC
;;(test (interp (plusC (numC 10) (appC (fdC 'const5 '_ (numC 5)) (numC 10))) 
;;              empty-env) 
;;      (numV 15)) 
;;
;;(test/exn (interp (appC (fdC 'f1 'x (appC (fdC 'f2 'y (plusC (idC 'x) (idC 'y))) 
;;                                          (numC 4))) 
;;                        (numC 3)) 
;;                  empty-env) 
;;          "lookup: symbol not found: 'x") 
;;
;;(define nested-fdC (fdC 'f1 'x 
;;                        (fdC 'f2 'x 
;;                             (plusC (idC 'x) (idC 'x)))))
;;(test (interp  nested-fdC
;;               empty-env) (funV 'f1 'x (fdC 'f2 'x (plusC (idC 'x) (idC 'x)))))
;;
;;(test (interp  (appC nested-fdC 
;;                     (numC 4)) 
;;               empty-env) (funV 'f2 'x (plusC (idC 'x) (idC 'x))))
;;
;;;we’re again failing to faithfully capture what substitution would have done. A function value needs to remember the substitutions that have already been applied to it. Because we’re representing substitutions using an environment, a function value therefore needs to be bundled with an environment. This resulting data structure is called a closure.
;;; this fails (when using fdC and funV
;;(test/exn (interp (appC (appC (fdC 'f1 'x 
;;                                   (fdC 'f2 'y 
;;                                        (plusC (idC 'x) (idC 'y)))) 
;;                              (numC 4)) 
;;                        (numC 5)) 
;;                  empty-env) "lookup: symbol not found: 'x")
;; but this works:
;;((λ (x) 
;;   ((λ (y) 
;;      (+ x y)) 
;;    4)) 
;; 5)
;
;;; did not work:
;;But one moment. What happens if we try the same example in our environment-based interpreter?
;;Do Now!
;;Observe that it works correctly: it reports an unbound identifier error. Environments automatically implement capture-free substitution!
;
;(define subst-again (appC (lamC 'f (lamC 'x (appC (idC 'f) (numC 10)))) (lamC 'y (plusC (idC 'x) (idC 'y)))))
;

;;;
;;;; Chapter 6
;;;;
;
;(define-type Binding
;  [bind (name : symbol) (val : number)])
;
;(define-type-alias Env (listof Binding))
;(define empty-env empty)
;(define extend-env cons)
;
;(define-type ExprC
;  [numC (n : number)]
;  [idC (s : symbol)]
;  [appC (fun : symbol) (arg : ExprC)]
;  [plusC (l : ExprC) (r : ExprC)]
;  [multC (l : ExprC) (r : ExprC)]
;  )
;
;(define-type FunDefC
;  [fdC (name : symbol) (arg : symbol) (body : ExprC)])
;
;(define (get-fun-def [fun : symbol] [fds : (listof FunDefC)]) : FunDefC
;  (if (empty? fds)
;      (error 'get-fun-def (string-append "ERR: function definition NOT found: " (to-string fun)))
;      (if (equal? fun (fdC-name (first fds)))
;          (first fds)
;          (get-fun-def fun (rest fds)))))
;
;(define (lookup [s : symbol] [env : Env]) : number
;  (if (empty? env)
;      (error 'lookup (string-append "ERR: unbound identifier: " (to-string s)))
;      (if (equal? s (bind-name (first env)))
;          (bind-val (first env))
;          (lookup s (rest env)))))
;
;(define (interp [e : ExprC] [env : Env] [fds : (listof FunDefC)]) : number
;  (type-case ExprC e
;    [numC (n) n]
;    [plusC (l r) (+ (interp l env fds) (interp r env fds))]
;    [multC (l r) (* (interp l env fds) (interp r env fds))]
;    [idC (s) (lookup s env)]
;; This version will cause the following (test/exn) to fail since the env keeps growing and doesn't handle scope properly
;;    [appC (f a) (local ([define fd (get-fun-def f fds)])
;;                  (interp (fdC-body fd) 
;;                          (extend-env 
;;                           (bind (fdC-arg fd) (interp a env fds)) 
;;                           env) 
;;                          fds))]
;    [appC (f a) (local ([define fd (get-fun-def f fds)])
;                  (interp (fdC-body fd) 
;                          (extend-env 
;                           (bind (fdC-arg fd) (interp a env fds)) 
;                           empty-env) 
;                          fds))]
;    ))
;
;(test (interp (plusC (numC 10) (appC 'const5 (numC 10))) 
;              empty-env 
;              (list (fdC 'const5 '_ (numC 5)))) 
;      15) 
;
;(test (interp (plusC (numC 10) (appC 'double (plusC (numC 1) (numC 2)))) 
;              empty-env 
;              (list (fdC 'double 'x (plusC (idC 'x) (idC 'x))))) 
;      16) 
;
;(test (interp (plusC (numC 10) (appC 'quadruple (plusC (numC 1) (numC 2)))) 
;              empty-env 
;              (list (fdC 'quadruple 'x (appC 'double (appC 'double (idC 'x)))) 
;                    (fdC 'double 'x (plusC (idC 'x) (idC 'x))))) 
;      22) 
;
;(test/exn (interp (appC 'f1 (numC 3)) 
;                  empty-env 
;                  (list (fdC 'f1 'x (appC 'f2 (numC 4))) 
;                        (fdC 'f2 'y (plusC (idC 'x) (idC 'y)))))
;          "lookup: ERR: unbound identifier: 'x")
;
;;; type in interaction window and huh?? how come z is bound to the first value of y??
;;(define y 1) 
;;(define f (let ((z y)) (λ (x) (begin
;;                                  (display (to-string x))
;;                                  (display (to-string y))
;;                                  (display (to-string z))
;;                                  (+ x (+ y z)))))) 
;;(define y 2)
;
;;;;
;;;; Chapter 5
;;;;
;
;(define-type ExprC
;  [numC (n : number)]
;  [idC (s : symbol)]
;  [appC (fun : symbol) (arg : ExprC)]
;  [plusC (l : ExprC) (r : ExprC)]
;  [multC (l : ExprC) (r : ExprC)]
;  )
;
;(define-type FunDefC
;  [fdC (name : symbol) (arg : symbol) (body : ExprC)])
;
;(define (get-fun-def [fun : symbol] [fds : (listof FunDefC)]) : FunDefC
;  (if (empty? fds)
;      (error 'get-fun-def (string-append "ERR: function definition NOT found: " (to-string fun)))
;      (if (equal? fun (fdC-name (first fds)))
;          (first fds)
;          (get-fun-def fun (rest fds)))))
;
;(define (subst [actual-param : ExprC] [formal-param : symbol] [in-fun-body : ExprC]) : ExprC
;  (type-case ExprC in-fun-body
;    [numC (n) (numC n)]
;    [idC (s) (cond 
;               [(symbol=? s formal-param) actual-param]
;               [else in-fun-body])]
;    [appC (f a) (appC f (subst actual-param formal-param a))]
;    [plusC (l r) (plusC (subst actual-param formal-param l) (subst actual-param formal-param r))]
;    [multC (l r) (multC (subst actual-param formal-param l) (subst actual-param formal-param r))]))
;
;(define (subst-eager [actual-param : number] [formal-param : symbol] [in-fun-body : ExprC]) : ExprC
;  (type-case ExprC in-fun-body
;    [numC (n) (numC n)]
;    [idC (s) (cond 
;               [(symbol=? s formal-param) (numC actual-param)]
;               [else in-fun-body])]
;    [appC (f a) (appC f (subst-eager actual-param formal-param a))]
;    [plusC (l r) (plusC (subst-eager actual-param formal-param l) (subst-eager actual-param formal-param r))]
;    [multC (l r) (multC (subst-eager actual-param formal-param l) (subst-eager actual-param formal-param r))]))
;
;(define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
;  (type-case ExprC e
;    [numC (n) n]
;    [idC (s) (error 'interp (string-append "ERR: unbound id: " (to-string s)))]
;    ;; lazy version
;    ;[appC (f a) (local ([define fd (get-fun-def f fds)])
;    ;              (interp (subst a (fdC-arg fd) (fdC-body fd)) fds))]
;    [appC (f a) (local ([define fd (get-fun-def f fds)])
;                  (interp (subst (numC (interp a fds)) (fdC-arg fd) (fdC-body fd)) fds))]
;    [plusC (l r) (+ (interp l fds) (interp r fds))]
;    [multC (l r) (* (interp l fds) (interp r fds))]
;    
;    ))
;
;;=================================
;
;(define-type ArithC
;  [numC (n : number)]
;  [plusC (l : ArithC) (r : ArithC)]
;  [multC (l : ArithC) (r : ArithC)]
;  [if0C (test-expr : ArithC) (true-expr : ArithC) (false-expr : ArithC)])
;
;(define-type ArithS
;  [numS (n : number)]
;  [plusS (l : ArithS) (r : ArithS)]
;  [multS (l : ArithS) (r : ArithS)]
;  [bminusS (l : ArithS) (r : ArithS)]
;  [uminusS (e : ArithS)]
;  [if0S (test-expr : ArithS) (true-expr : ArithS) (false-expr : ArithS)])
;
;(define (parseS [s : s-expression]) : ArithS
;  (cond
;    [(s-exp-number? s) (numS (s-exp->number s))]
;    [(s-exp-list? s) 
;     (let ([s1 (s-exp->list s)])
;       (cond 
;         [(= (length s1) 2) 
;          (case (s-exp->symbol (first s1))
;            [(-) (uminusS (parseS (second s1)))]
;            [else (error 'parseS "unknown unary operator")])]
;         [(= (length s1) 3)
;          (case (s-exp->symbol (first s1))
;            [(+) (plusS (parseS (second s1)) (parseS (third s1)))]
;            [(*) (multS (parseS (second s1)) (parseS (third s1)))]
;            [(-) (bminusS (parseS (second s1)) (parseS (third s1)))]
;            [else (error 'parse "unknown binary operator")])]
;         [(= (length s1) 4)
;          (case (s-exp->symbol (first s1))
;            [(if0) (if0S (parseS (second s1)) (parseS (third s1)) (parseS (fourth s1)))]
;            [else (error 'parseS "unknown quad operator")])]
;         [else (error 'parseS (string-append "unknown number of operators: " (to-string (length s1))))]))]
;    [else (error 'parseS "invalid expression")]))
;
;(define (interp [a : ArithC]) : number
;  (type-case ArithC a
;    [numC (n) n]
;    [plusC (l r) (+ (interp l) (interp r))]
;    [multC (l r) (* (interp l) (interp r))]
;    [if0C (a b c) (if (= 0 (interp a)) (interp b) (interp c))]))
;
;(define (desugar [a : ArithS]) : ArithC
;  (type-case ArithS a
;    [numS (n) (numC n)]
;    [plusS (l r) (plusC (desugar l) (desugar r))]
;    [multS (l r) (multC (desugar l) (desugar r))]
;    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
;    [uminusS (e) (multC (numC -1) (desugar e))]
;    [if0S (a b c) (if0C (desugar a) (desugar b) (desugar c))]))

;;;;
;;;; Chapter 4
;;;;
;(define-type ArithC
;  [numC (n : number)]
;  [plusC (l : ArithC) (r : ArithC)]
;  [multC (l : ArithC) (r : ArithC)])
;
;(define-type ArithS
;  [numS (n : number)]
;  [plusS (l : ArithS) (r : ArithS)]
;  [multS (l : ArithS) (r : ArithS)]
;  [bminusS (l : ArithS) (r : ArithS)]
;  [uminusS (e : ArithS)])
;
;(define (desugar [as : ArithS]) : ArithC
;  (type-case ArithS as
;    [numS (n) (numC n)]
;    [plusS (l r) (plusC (desugar l) (desugar r))]
;    [multS (l r) (multC (desugar l) (desugar r))]
;    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
;    ;[uminusS (e) (desugar (bminusS (numS 0) e))]
;    ;[uminusS (e) (bminusS (numS 0) (desugar e))]
;    [uminusS (e) (multC (numC -1) (desugar e))]))
;
;(define (parseS [s : s-expression]) : ArithS
;  (cond
;    [(s-exp-number? s) (numS (s-exp->number s))]
;    [(s-exp-list? s) 
;     (let ([s1 (s-exp->list s)])
;       (cond 
;         [(= (length s1) 2) 
;          (case (s-exp->symbol (first s1))
;            [(-) (uminusS (parseS (second s1)))]
;            [else (error 'parseS "unknown unary operator")])]
;         [(= (length s1) 3)
;          (case (s-exp->symbol (first s1))
;            [(+) (plusS (parseS (second s1)) (parseS (third s1)))]
;            [(*) (multS (parseS (second s1)) (parseS (third s1)))]
;            [(-) (bminusS (parseS (second s1)) (parseS (third s1)))]
;            [else (error 'parse "unknown binary operator")])]
;         [else (error 'parseS "unkown number of operators")]))]
;    [else (error 'parseS "invalid expression")]))
;
;(define (interp [a : ArithC]) : number
;  (type-case ArithC a
;    [numC (n) n]
;    [plusC (l r) (+ (interp l) (interp r))]
;    [multC (l r) (* (interp l) (interp r))]))
;
;(test (interp (desugar (parseS '(- 40)))) -40)
;(test (interp (desugar (parseS '(- (* (- 9 4) (+ 2 6)))))) -40)
;
;;;;
;;;; Chapter 3
;;;;
;
;(define-type ArithC
;  [numC (n : number)]
;  [plusC (l : ArithC) (r : ArithC)]
;  [multC (l : ArithC) (r : ArithC)])
;
;(define (interp [a : ArithC]) : number
;  (type-case ArithC a
;    [numC (n) n]
;    [plusC (l r) (+ (interp l) (interp r))]
;    [multC (l r) (* (interp l) (interp r))]))
;
;(define (parse [s : s-expression]) : ArithC
;  (cond
;    [(s-exp-number? s) (numC (s-exp->number s))]
;    [(s-exp-list? s) 
;     (let ([s1 (s-exp->list s)])
;       (case (s-exp->symbol (first s1))
;         [(+) (plusC (parse (second s1)) (parse (third s1)))]
;         [(*) (multC (parse (second s1)) (parse (third s1)))]
;         [else (error 'parse "invalid list input")]))]
;    [else (error 'parse "invalid input")]))

;;;
;;;; Chapter 2
;;;;
;(define l '(+ 1 2))
;(define f (first (s-exp->list l)))
;(define f1 (s-exp->symbol (first (s-exp->list l))))
;(define f2 (s-exp->number (second (s-exp->list l))))
;(define f3 (s-exp->number (third (s-exp->list l))))
;(define f-1 (symbol->string(s-exp->symbol (first (s-exp->list l)))))
;
;(define-type ArithC
;  [numC (n : number)]
;  [plusC (l : ArithC) (r : ArithC)]
;  [multC (l : ArithC) (r : ArithC)])
;
;(define a-1 (numC 23))
;(define a-2 '(+ 2 4))
;
;
;(define (parse [s : s-expression]) : ArithC
;  (cond
;    [(s-exp-number? s) (numC (s-exp->number s))]
;    [(s-exp-list? s) 
;     (let ([s1 (s-exp->list s)])
;       (case (s-exp->symbol (first s1))
;         [(+) (plusC (parse (second s1)) (parse (third s1)))]
;         [(*) (multC (parse (second s1)) (parse (third s1)))]
;         [else (error 'parse "invalid list input")]))]
;    [else (error 'parse "invalid input")]))
;
;(parse l)

;;;;
;;;; Chapter 1
;;;;
;
;(define-type MisspelledAnimal
;  [caml (humps : number)]
;  [yacc (height : number)])
;
;(define ma-1 : MisspelledAnimal (caml 3))
;(define ma-2 : MisspelledAnimal (yacc 4.9))
;
;(define ma1 (caml 3))
;(define ma2 (yacc 2.7))
;
;(define (good? [ma : MisspelledAnimal]) : boolean
;  (type-case MisspelledAnimal ma
;    [caml (humps) (>= humps 2)]
;    [yacc (height) (> height 2.1)]))
;
;;(test (good? ma1) #t)
;;(test (good? ma2) #t)
;
;(define-type MisspelledAnimal-2
;  [caml2 (humps-of-caml : number)]
;  [yacc2 (height-of-yacc : number)])
;
;(define (good2? [ma : MisspelledAnimal-2]) : boolean
;  (type-case MisspelledAnimal-2 ma
;    [yacc2 (height) (>= height 2.1)]
;    [caml2 (humps) (> humps 2)]))
;
;(define ma-3 : MisspelledAnimal-2 (caml2 1))
;(define ma-4 : MisspelledAnimal-2 (yacc2 2.1))
;
;;(test (good2? ma-4) #t)
;;(test (good2? ma-3) #f)
;
;(define (good3? [ma : MisspelledAnimal]) : boolean
;  (cond
;    [(caml? ma) (>= (caml-humps ma) 1)]
;    [(yacc? ma) (> (yacc-height ma) 2.1)]))
;
;;(test (good3? ma1) #t)
;;(test (good3? ma2) #t)
;
