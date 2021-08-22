#lang racket
; Holds proofs for various propositional logic theorems
(require "main.rkt")

(define reflexivity
  (start (implication (proposition "A") (proposition "A"))
         (assume-hyp "hyp"
                     (apply (get-var "hyp") (end)))))

(define transitivity-implies
  (start (implication (implication (proposition "A") (proposition "B"))
                      (implication (implication (proposition "B") (proposition "C"))
                                   (implication (proposition "A") (proposition "C"))))
         (assume-hyp "A-B"
                     (assume-hyp "B-C"
                                 (assume-hyp "A"        
                                             (let "B"
                                               (modus-ponens (get-var "A") (get-var "A-B"))
                                               (let "C"
                                                 (modus-ponens (get-var "B") (get-var "B-C"))
                                                 (apply (get-var "C") (end)))))))))

(define transitivity-conjunction
  (start (implication (conjunction (conjunction (proposition "A") (proposition "B"))
                                   (conjunction (proposition "B") (proposition "C")))
                      (conjunction (proposition "A") (proposition "C")))
         (assume-hyp "AB&BC"
                     (split
                      (let "AB" (take 0 (get-var "AB&BC"))
                        (apply (take 0 (get-var "AB")) (end)))
                      (let "BC" (take 1 (get-var "AB&BC"))
                        (apply (take 1 (get-var "BC")) (end)))))))