#lang racket/base

(require syntax/parse)
(require racket/generic)

(provide (all-defined-out))

(define-generics syntaxable
  (->stx syntaxable))

;; The syntax representation of types
(struct Type ())
(define-syntax-rule (base-type tc-name rep rt)
  (struct tc-name Type ()
    #:methods gen:custom-write
    [(define (write-proc t p m) (display rep p))]
    #:methods gen:syntaxable
    [(define (->stx x) rt)]))

(base-type DynT "Dyn" #'(rt:Dyn))
(base-type BoolT "Bool" #'(rt:Bool))
(base-type IntT "Int" #'(rt:Int))
(struct FunT Type (formals return)
  #:methods gen:custom-write
  [(define (write-proc t p m)
     (display `(,@(FunT-formals t) -> ,(FunT-return t)) p))]
  #:methods gen:syntaxable
  [(define/generic gen->stx ->stx)
   (define (->stx t)
     (with-syntax ([(t* ...) (map gen->stx (FunT-formals t))])
       #`(rt:Fun `(,t* ...) #,(gen->stx (FunT-return t)))))])

;; Because I don't want to write so many parens
(define DYN (DynT))
(define BOOL (BoolT))
(define INT (IntT))

(define-splicing-syntax-class type
  #:commit
  (pattern (~literal Dyn)  #:attr value DYN)
  (pattern (~literal Int)  #:attr value INT)
  (pattern (~literal Bool) #:attr value BOOL)
  (pattern (x:type ... (~literal ->) r:type)
           #:attr value
           (FunT (attribute x.value) (attribute r.value))))

(define-splicing-syntax-class lambda-formal
  #:attributes (name)
  #:description
  "formal parameter of a lambda with or without an annotation"
  (pattern (id:id (~datum :) t:type)
           #:attr name (syntax-property #'id 'type (attribute t.value)))
  (pattern id:id
           #:attr name (syntax-property #'id 'type DYN)))


(require racket/match)
;; consistent will always be type, type -> Bool
(define (consistent? t g)
  (match* (t g)
    [((DynT) _) #t]
    [(_ (DynT)) #t]
    [((IntT) (IntT)) #t]
    [((BoolT) (BoolT)) #t]
    [((FunT t-args t-ret) (FunT g-args g-ret))
     (define (c*? t g)
       (or (and (null? t) (null? g))
           (and (pair? t) (pair? g)
                (consistent? (car t) (car g))
                (c*? (cdr t) (cdr g)))))
     (and (c*? t-args g-args)
          (consistent? t-ret g-ret))]))

;; join recusively finds the most precise type that is
;; consistent with both types or raises a type error
(define (join t g)
  (match* (t g)
    [((DynT) _) g]
    [(_ (DynT)) t]
    [((IntT) (IntT)) INT]
    [((BoolT) (BoolT)) BOOL]
    [((FunT t-args t-ret) (FunT g-args g-ret))
     ;; consider adding support for auto-currying
     (let ([lt (length t-args)]
           [lg (length g-args)])
       (cond
         [(= (length t-args) (length g-args))
          (FunT (map join t-args g-args) (join t-ret g-ret))]
         [else (raise-static-type-error)]))]
    [(other wise) (raise-static-type-error)]))

;; utilities that may need to be shared if this goes any further
(define (const a) (lambda b a))
(define (flip f) (lambda (a b) (f b a)))

(define stx-type
  (case-lambda
    [(stx ty) (syntax-property stx 'type ty)]
    [(stx)
     (let ([type (syntax-property stx 'type)])
       (if (Type? type)
           type
           (error 'stx-type "lookup for ~a retrieved ~a" stx type)))]))

;; simple-datum->Type takes any datum and returns the type of that datum or false
(define (simple-datum->type d)
  (cond
    [(fixnum? d) INT]
    [(boolean? d) BOOL]
    [else #f]))

;; type check and insert implicit casts
(define (type-check/insert-casts stx)
  (tc/cst stx (initial-type-environment)))

(require (prefix-in t: (for-meta -1 racket/base)))
(require (prefix-in rt: (for-meta -1 "./runtime.rkt")))
(require (for-meta -1 racket/base))

(define (tc/cst stx env)
  (parameterize ([current-syntax stx])
    (syntax-case stx (t:#%plain-app t:#%plain-lambda t:quote t:#%expression t:if)
      [var (identifier? #'var) (values #'var (lookup env #'var))]
      [(t:#%plain-lambda (id ...) body)
       (tc/cst-lambda #'(id ...) #'body env)]
      [(t:#%plain-app rator rand* ...)
       (tc/cst-app #'rator #'(rand* ...) env)]
      [(t:quote datum) (tc/cst-datum #'datum)]
      [(t:#%expression stx)
       (let-values ([(stx ty) (tc/cst #'stx env)])
         (values (stx-type stx ty) ty))]
      [(t:if t c a) (tc/cst-if #'t #'c #'a env)]
      [other (error 'tc/cst "unexpected value: ~a" #'other)])))

;; helpers to make tc/cst slightly more flexible
(define (tc/cst* stx* env)
  (for/lists (stx* ty*) ([stx (in-list stx*)])
    (tc/cst stx env)))

;; How to typecheck a lambda
(define (tc/cst-lambda ids body env)
  ;; get type annotations on formals
  (let*-values ([(id*) (syntax->list ids)]
                [(env) (extend* env id*)]
                ;; Typecheck the body with the extended environment
                [(body retT) (tc/cst body env)]
                ;; build funtion type and resulting syntax
                [(lamT) (FunT (map stx-type id*) retT)]
                [(lam) #`(t:#%plain-lambda #,ids #,body)]
                [(lam) (stx-type lam lamT)])
    (values lam lamT)))

;; how to typecheck a if
(define (tc/cst-if test conseq alt env)
  ;; get type annotations on formals
  (define if-stx (current-syntax))
  (parameterize ([current-syntax test]
                 [current-formatter (default-formatter 'test)])
    (let*-values ([(t ty) (tc/cst test env)]
                  [(t) (make-cast t ty BOOL)])
      (parameterize ([current-syntax if-stx]
                     [current-formatter (default-formatter 'branch)])
        (let*-values ([(c cty) (tc/cst conseq env)]
                      [(a aty) (tc/cst alt env)]
                      [(jty) (join cty aty)]
                      [(c) (make-cast c cty jty)]
                      [(a) (make-cast a aty jty)])
          (values #`(if #,t #,c #,a) jty))))))


;; How to typececk a application
(define (tc/cst-app rator rand* env)
  ;; The actual well typed rule for application
  ;; Takes the type of the typecheck subparts and
  ;; returns the type they should be casted to.
  (define (app-cast-rule ratorT randT*)
    (cond
      [(DynT? ratorT)
       (let ([expectT* (map (const DYN) randT*)])
         (values (FunT  expectT* DYN) expectT*))]
      [(FunT? ratorT)
       (if (= (length (FunT-formals ratorT)) (length randT*))
           (values ratorT (FunT-formals ratorT))
           (raise-static-type-error))]
      [else (raise-static-type-error)]))
  ;; typecheck all subparts
  (parameterize ([current-formatter (default-formatter 'application)])
    (let*-values ([(rator ratorT) (tc/cst rator env)]
                  [(rand* randT*) (tc/cst* (syntax->list rand*) env)]
                  ;; apply the standard typing rule
                  [(ratorT^ randT^*) (app-cast-rule ratorT randT*)]
                  ;; cast everything to the expected type
                  [(rator) (make-cast rator ratorT ratorT^)]
                  [(rand*) (make-cast* rand* randT* randT^*)]
                  ;; construct the result type and syntax
                  [(appT) (FunT-return ratorT^)]
                  [(app) #`(t:#%plain-app #,rator . #,rand*)]
                  [(app) (stx-type app appT)])
      (values app appT))))


(define (tc/cst-datum datum)
  (let* ([d   (syntax->datum datum)]
         [ty  (or (simple-datum->type d) (raise-unsupported-datum d))])
    (with-syntax ([da  (stx-type datum ty)])
      (with-syntax ([dr  (stx-type (syntax/loc datum (t:quote da)) ty)])
        (values #'dr ty)))))

(define (make-cast exp t1 t2)
  (if (equal? t1 t2)
      exp
      (cast exp t1 t2)))

(define (cast exp t1 t2)
  #`(rt:cast #,exp #,(->stx t1) #,(->stx t2) #,(make-blame-label)))

#;
(define (type->stx t)
  (match t
    [(DynT) #'(rt:type:dyn)]
    [(IntT) #'(rt:type:int)]
    [(BoolT) #'(rt:type:bool)]
    [(FunT fml* ret)
     #`(rt:type:fun #,(map type->stx fml*) #,(type->stx ret))]
    [other (error 'types/type->stx "match error: ~a" other)]))

(define (make-cast* exp* t1* t2*)
  (map make-cast exp* t1* t2*))

;; errors raised by typechecking use the context, message, and syntax
;; for error reporting in and out of the runtime
(define current-syntax
  (make-parameter
   #'unkown-syntax
   (lambda (stx)
     (if (syntax? stx)
         stx
         (error 'current-context "expexted syntax got ~a" stx)))))

(define ((default-formatter context) stx)
  (format "inconsistent types in ~a at ~a\n\t~a"
          context
          (srcloc->string (syntax->srcloc stx))
          (syntax->datum stx)))

(define current-formatter
  (make-parameter
   (lambda (stx)
     (format "blame: ~a" stx))
   (lambda (p)
     (if (procedure? p)
         (lambda (stx)
           (if (syntax? stx)
               (let ([r (p stx)])
                 (if (string? r)
                     r
                     (error 'current-formatter "expected string got ~a" r)))
               (error 'current-formatter "expectected syntax got ~a" stx)))
         (error 'current-formatter "expected procedure got ~a" p)))))

(define (make-blame-label)
  (datum->syntax (current-syntax) ((current-formatter) (current-syntax))))

(define (raise-static-type-error)
  (error 'blame ((current-formatter) (current-syntax))))

;; errors in typechecking and
(define (raise-unsupported-datum datum)
  (error 'type-check "unsupported literal ~a" datum))

(define arity-fmt
  "incorrect arrity in application ...\n\tin application of type ~a to types ~a")

(define app-inc-fmt
  "attempt to apply type ~a which is inconsistent with function type")

(define (current-syntax-location)
  (let ([stx (current-syntax)])
    (srcloc->string
     (srcloc
      (syntax-source stx)
      (syntax-line stx)
      (syntax-column stx)
      (syntax-position stx)
      (syntax-span stx)))))

;; Environment Helpers
(require syntax/id-table)
(define (initial-type-environment)
  (let* ([env (make-immutable-free-id-table)]
         [env (free-id-table-set env #'t:+ (FunT (list INT INT) INT))]
         [env (free-id-table-set env #'t:- (FunT (list INT INT) INT))]
         [env (free-id-table-set env #'t:* (FunT (list INT INT) INT))]
         [env (free-id-table-set env #'t:= (FunT (list INT INT) BOOL))]
         )
    env))

(define (extend env i)
  (free-id-table-set env i (syntax-property i 'type)))

(define (extend* env i*)
  (foldl (flip extend) env i*))

(define (lookup env i)
  (free-id-table-ref env i))

(define (syntax->srcloc stx)
  (srcloc (syntax-source stx)
          (syntax-line stx)
          (syntax-column stx)
          (syntax-position stx)
          (syntax-span stx)))
