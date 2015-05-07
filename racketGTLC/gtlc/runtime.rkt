#lang racket

(provide (all-defined-out))

;; our simple type system
(define-syntax-rule (base-type name)
  (struct name ()
    #:transparent
    #:methods gen:custom-write
    [(define (write-proc t p n) (display (~a 'name) p))]))

(base-type Dyn)
(base-type Int)
(base-type Bool)

(struct Fun (formals return)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc t p n)
     (display `(,@(Fun-formals t) -> ,(Fun-return t)) p))])

(struct ptr (value type)
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc t p m) (display (ptr-value t) p))])

(define (cast v t1 t2 l)
  (define (arity=? l1 l2)
    (or (and (null? l1) (null? l2))
        (and (pair? l1) (pair? l2)
             (arity=? (cdr l1) (cdr l2)))))
  (cond
    ;; cast between structurally equal casts are noops
    [(equal? t1 t2) v]
    ;; projection from dyn
    [(Dyn? t1) (cast (ptr-value v) (ptr-type v) t2 l)]
    ;; injection to dyn
    [(Dyn? t2) (ptr v t1)]
    ;; recursive types need special handling
    [(and (Fun? t1) (Fun? t2))
     (let ([t1* (Fun-formals t1)]
           [t2* (Fun-formals t2)]
           [r1  (Fun-return t1)]
           [r2  (Fun-return t2)]
           [recur (lambda (v^ t1^ t2^) (cast v^ t1^ t2^ l))])
       (if (arity=? t1* t2*)
           (lambda a
             (recur (apply v (map recur a t2* t1*)) r1 r2))
           (error 'blame/arity l)))]
    [else (flush-output (current-output-port)) (error 'blame l)]))