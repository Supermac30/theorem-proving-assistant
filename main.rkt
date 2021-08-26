#lang racket
(provide (all-defined-out))

; Types
(struct type () #:transparent)
(struct natural type () #:transparent)
(struct boolean type () #:transparent)
(struct to (type0 type1) #:transparent)
(struct prod (type0 type1) #:transparent)

; boolean expressions and operations
(struct proposition boolean (value) #:transparent)
(struct conjunction boolean (prop0 prop1) #:transparent)
(struct disjunction boolean (prop0 prop1) #:transparent)
(struct implication boolean (prop0 prop1) #:transparent)
(struct negation boolean (prop))

#| Boolean Expressions:
    (proposition value) - Holds a boolean value representing some proposition value. value is a string.
    (conjunction prop0 prop1) - Holds a conjunction of two boolean expressions.
    (disjunction prop0 prop1) - Holds a disjunction of two boolean expressions.
    (implication prop0 prop1) - Holds the expression prop0 implies prop1, where prop0 and prop1 are boolean expressions.
    (negation prop) - Holds the negation of the boolean expression prop.

   Natural Numbers & Operations:
    (zero) - Holds the number zero
    (succ n) - Holds the successor of the number n

TODO: Finish basic documentation of each struct
TODO: Write documentation for semantics of the proofs
|#

; natural numbers and operations
(struct zero natural () #:transparent)
(struct succ natural (value) #:transparent)
(struct True boolean () #:transparent)
(struct False boolean () #:transparent)

; identifiers
(struct identifier () #:transparent)
(struct start identifier (statement proof) #:transparent)
(struct end identifier () #:transparent)

; expressions
(struct expression () #:transparent)
(struct get-var expression (name) #:transparent)
(struct modus-ponens expression (hypo impl) #:transparent)
(struct take expression (pos prop) #:transparent)

; statements
(struct statement () #:transparent)
(struct take-conc statement (pos rest) #:transparent)
(struct let statement (name prop rest) #:transparent)
(struct apply statement (prop rest) #:transparent)
(struct split statement (left right) #:transparent)
(struct to-false statement (rest) #:transparent)
(struct assume-hyp statement (name rest) #:transparent)
(struct print-exp statement (prop rest) #:transparent) ; For the purpose of debugging

(struct func (type arg body) #:transparent)
(struct rec-func (name type arg base-case rec-case) #:transparent)
(struct input (func arg) #:transparent)
(struct left (arg) #:transparent)
(struct right (arg) #:transparent)
(struct pair (arg0 arg1) #:transparent)

(struct induction (var base-case inductive-case))
(struct expand (rest))

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
        [else (raise "Cannot call eval-prop without a proposition")]))

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
  (letrec ([sub-into-body (lambda (arg name body)
                            (match body
                              [(get-var name) arg]
                              [(get-var other-name) (get-var other-name)]
                              [(left inner) (left (sub-into-body arg name inner))]
                              [(right inner) (right (sub-into-body arg name inner))]
                              [(pair l r) (pair (sub-into-body arg name l) (sub-into-body arg name r))]
                              [(input inner-func name) (input inner-func name)] ; In this case, the variable is shadowed by an inner function and should not be replaced.
                              [(input inner-func other-name) (input (sub-into-body arg name inner-func) other-name)]
                              [_ (raise "Error when parsing input with sub-into-body.")]))]
                            
           [create-assumption (lambda (name prop) (hash-set assumptions name prop))]
           
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
                 (raise statement))] ; Fix so that (True) is recognised as a valid end
          
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
                                    (prove statement rest assumptions))]

      [(induction var base-case inductive-case) (let* ([base-case-statement (sub-into-body (zero) var statement)]
                                                       [inductive-case-statement (sub-into-body (succ var) var statement)]
                                                       [base-case-assumptions (hash-map assumptions ((curry sub-into-body) (zero) var))]
                                                       [inductive-case-assumptions (hash-map assumptions ((curry sub-into-body) (succ var var)))])
                                                  (and (prove base-case-statement base-case base-case-assumptions)
                                                       (prove inductive-case-statement inductive-case inductive-case-assumptions)))]
      
      [(expand rest) (if (input? statement)
                         (let* ([func (input-func statement)]
                                [arg (input-arg statement)])
                           (if (= (natural) (func-type (input-func statement))) ; In the case of a function that acts on natural numbers
                               (let* ([body (if (func? func) (sub-into-body arg (func-arg func) (func-body func))
                                               (match (input-arg statement)
                                                 [(zero) (rec-func-base-case func)]
                                                 [(succ n) (sub-into-body n (rec-func-arg func) (rec-func-rec-case func))]
                                                 [_ (raise "Cannot expand recursive function when case is not known. Use induction first.")]))])
                                 (prove body rest assumptions))
                               (raise "No other recursive type has been implemented yet.")))
                         (raise "Can only expand functions."))]
      
      [_ (raise "Cannot parse expression")])))

; TODO: Test expand and induction

; Default prove. Starts with an empty hash-map as the environment
(define (prove-from-start start)
  (prove (start-statement start) (start-proof start) (hash)))


; TODO
; - Create documentation for each struct
; - Build tests for the function prove
; - Create theorems that, after proven, can take in
;   multiple assumptions and result in a new assumption (!)
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

; - Remove all special cases for natural numbers and induction, so that the only time a proof by induction can
; be used is when we are 'inducting' on a natural number.

(define (eval-func func arg env)
  (letrec ([eval-body (lambda (body env)
                       (match body
                         [(input func arg) (eval-func (eval-body func env) (eval-body arg env) env)]
                         [(succ num) (succ (eval-body num env))]
                         [(get-var name) (hash-ref env name)]
                         [(left arg) (car (eval-body arg env))]
                         [(right arg) (cdr (eval-body arg env))]
                         [(pair arg0 arg1) (cons (eval-body arg0 env) (eval-body arg1 env))]
                         [(negation arg) (if (True? (eval-body arg env))
                                             (False)
                                             (True))]
                         [_ body]))])
    (cond [(func? func) (eval-body (func-body func) (hash-set env (func-arg func) arg))]
          [(rec-func? func) (match (rec-func-type func)
                              [(to (natural) _) (match arg
                                                  [(zero) (eval-body (rec-func-base-case func) env)]
                                                  [(succ n) (eval-body (rec-func-rec-case func)
                                                                       (hash-set (hash-set env (rec-func-name func) func)
                                                                                 (rec-func-arg func) n))])]
                              [_ (raise "recursive functions are only defined on integers")])]
          [true (raise "Can only evaluate functions")])))