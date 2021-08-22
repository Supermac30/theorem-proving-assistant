#lang racket
(provide (all-defined-out))

(struct proposition (value) #:transparent)
(struct conjunction (prop0 prop1) #:transparent)
(struct disjunction (prop0 prop1) #:transparent)
(struct implication (prop0 prop1) #:transparent)
(struct negation (prop))

; identifiers
(struct start (statement proof) #:transparent)
(struct end () #:transparent)

; expressions
(struct get-var (name) #:transparent)
(struct modus-ponens (hypo impl) #:transparent)
(struct take (pos prop) #:transparent)

; statements
(struct take-conc (pos rest) #:transparent)
(struct let (name prop rest) #:transparent)
(struct apply (prop rest) #:transparent)
(struct split (left right) #:transparent)
(struct to-false (rest) #:transparent)
(struct assume-hyp (name rest) #:transparent)
(struct print-exp (prop rest) #:transparent) ; For the purpose of debugging

; Warning: Works only on propositions without variable names, when only bools are stored on proposition
(define (eval-prop prop)
  (cond [(proposition? prop) (proposition-value prop)]
        [(conjunction? prop) (and (eval-prop (conjunction-prop0 prop))
                                  (eval-prop (conjunction-prop1 prop)))]
        [(disjunction? prop) (or (eval-prop (disjunction-prop0 prop))
                                 (eval-prop (disjunction-prop1 prop)))]
        [(implication? prop) (if (eval-prop (implication-prop0 prop))
                                 (eval-prop (implication-prop1 prop))
                                 true)]
        [(negation? prop) (if (eval-prop (negation-prop prop)) false true)]
        [true (raise "Cannot call eval-prop without a proposition")]))

; Negates without double negations. Not smart enough for Demorgan's laws (Add later?)
(define (negate prop) (if (negation? prop) (negation-prop prop) (negation prop)))

; Finds Contrapositive of an implication.
(define (contrapositive impl)
  (if (implication? impl)
      (implication (negate (implication-prop1 impl))
                   (negate (implication-prop0 impl)))
      (raise "Can only take the contrapositive of an implication")))

; Proves a statement. Returns true if the proof successfully proves the statement.
; An exception is raised otherwise.
(define (prove statement proof assumptions)
  (letrec ([create-assumption (lambda (name prop) (hash-set assumptions name prop))]
           
           [take-assumption (lambda (name) (hash-ref assumptions name))]
           
           [eval-expression (lambda (expression)
                              (match expression
                                [(get-var name) (take-assumption name)]
                                [(modus-ponens old-hypo old-impl)
                                 (let* ([impl (eval-expression old-impl)]
                                        [hypo (eval-expression old-hypo)])
                                   (if (implication? impl)
                                       (if (equal? hypo (implication-prop0 impl))
                                           (implication-prop1 impl)
                                           (raise "Cannot apply modus-ponens when hypotheses are not equal"))
                                       (raise "Can only apply modus ponens on an implication")))]
                                [(take pos prop)
                                 (let* ([conj (eval-expression prop)])
                                   (if (conjunction? conj)
                                       (if (= pos 0) (conjunction-prop0 conj) (conjunction-prop1 conj))
                                       (raise "Can only take from a conjunction")))]))])
    
    (match proof
      [(end) (if (and (boolean? statement) statement)
                 statement
                 (raise statement))]
          
      [(let name prop rest) (prove statement
                                   rest
                                   (create-assumption name (eval-expression prop)))]
          
      [(to-false rest) (prove false rest assumptions)]

      [(split left right) (if (conjunction? statement)
                              (and (prove (conjunction-prop0 statement)
                                          left
                                          assumptions)
                                   (prove (conjunction-prop1 statement)
                                          right
                                          assumptions))
                              (raise "Can only split conjunctions"))]

      [(take-conc pos rest) (prove (if (disjunction? statement)
                                       (if (= pos 0) (disjunction-prop0 statement) (disjunction-prop1 statement))
                                       (raise "Can only take-conc from a disjunction"))
                                   rest
                                   assumptions)]

      [(apply prop rest) (if (equal? statement (eval-expression prop))
                             (prove true
                                    rest
                                    assumptions)
                             (raise "Can only apply an assumption equal to the hypothesis"))]

      [(assume-hyp name rest) (if (implication? statement)
                                  (let* ([hyp (implication-prop0 statement)]
                                         [conc (implication-prop1 statement)])
                                    (prove conc
                                           rest
                                           (create-assumption name hyp)))
                                  (raise "Can only assume the hypothesis of an implication"))]

      [(print-exp prop rest) (begin (print (eval-expression prop))
                                    (prove statement rest assumptions))])))

; Default prove. Starts with an empty hash-map as the environment
(define (prove-from-start start)
  (prove (start-statement start) (start-proof start) (hash)))


; TODO
; - Build tests for the function prove
; - Create theorems that, after proven,
;   can take in multiple assumptions and result in a new assumption (!)
; - Build a bank of theorems to be used in proofs

; - Add support for proofs by contradiction
; - Build a proof argument that takes the contrapositive of the statement

; - Add support for sets and set operations
; - Add support for quantifiers
; - Add support for recursively defined sets
; - Use sets to build numbers
; - Define arithmetic

; - Build a REPL for proving statements and building up theorems
;   - This would store proved theorems in a new file to be used again later.
