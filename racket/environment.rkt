#lang racket

;; This module create the base enviroments for the user program

(provide (all-defined-out))
(require
 (for-syntax
  syntax/parse
  ;;racket/base
  "./types.rkt"))

(require racket/unsafe/ops)
(provide unsafe-fx+ unsafe-fx-)


(define-syntax (gradual-datum stx)
  (syntax-case stx ()
    [(_ . s)
     (let ([d (syntax->datum #'s)])
       ;; I only wish to deal with a few primitives for now
       (if (or (fixnum? d) (boolean? d))
           (syntax/loc stx (#%datum . s))
           (raise-syntax-error #'s)))]))

(define-syntax (gradual-lambda stx)
  (syntax-parse stx
    [(lam (fml:lambda-formal ...) body)
     (quasisyntax/loc stx (lambda #,(attribute fml.name) body))]))

(define-syntax (gradual-apply stx)
  (syntax-parse stx
    [(app rator rands ...) (syntax/loc stx (#%plain-app rator rands ...))]))

;; mimic the first order nature of schml primitives
(require racket/fixnum)
(define-syntax (gradual-plus stx)
  (syntax-parse stx
    [(p n m) #'(unsafe-fx+ n m)]))

(define-syntax (gradual-minus stx)
 ;; (print 'minus) (newline)
  (syntax-parse stx
    [(p n m) #'(unsafe-fx- n m)]))

