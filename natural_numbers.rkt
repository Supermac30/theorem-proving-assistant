#lang racket
; Holds functions and proofs for natural numbers
(require "main.rkt")

(define predecessor
  (rec-func "predecssor"
            (to (natural) (natural))
            "num"
            (zero)
            (get-var "num")))

(define add-func
  (func (to (prod (natural) (natural)) (natural))
        "nums"
        (input (rec-func "add-n"
                         (to (natural) (natural))
                         "n"
                         (left (get-var "nums"))
                         (succ (input (get-var "add-n")
                                      (get-var "n"))))
               (right (get-var "nums")))))

(define (add num0 num1)
  (input add-func (pair num0 num1)))

(define double-func
  (func (to (natural) (natural))
        "num"
        (add (get-var "num") (get-var "num"))))

(define (double n)
  (input double-func n))

(define power-of-2-func
  (rec-func "power-of-2-func"
            (to (natural) (natural))
            "n"
            (succ (zero))
            (double (input (get-var "power-of-2-func")
                           (get-var "n")))))

(define mult-func
  (func (to (prod (natural) (natural)) (natural))
        "nums"
        (input (rec-func "mult-n"
                         (to (natural) (natural))
                         "n"
                         (zero)
                         (add (input (get-var "mult-n") (get-var "n"))
                              (left (get-var "nums"))))
               (right (get-var "nums")))))

(define (mult num0 num1)
  (input mult-func (pair num0 num1)))

(define pow-func
  (func (to (prod (natural) (natural)) (natural))
        "nums"
        (input (rec-func "mult-n"
                         (to (natural) (natural))
                         "n"
                         (succ (zero))
                         (mult (input (get-var "mult-n") (get-var "n"))
                               (left (get-var "nums"))))
               (right (get-var "nums")))))

(define (pow num0 num1)
  (input pow-func (pair num0 num1)))

(define (display-num n)
  (match n
    [(zero) 0]
    [(succ m) (+ 1 (display m))]))

(define is-even
  (rec-func "is-even"
            (to (natural) (natural))
            "num"
            (True)
            (negation (input (get-var "is-even")
                             (get-var "num")))))

(define tautology0
  (start (input is-even (zero))
         (expand (end))))

