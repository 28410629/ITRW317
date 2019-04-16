(deftemplate variable
    (slot name)
    (slot negative)
)

(deftemplate _applyNegativeVariable
    (slot variable)
)

(deftemplate _applyNegativeOr
    (slot variable1)
    (slot variable2)
)

(deftemplate _applyNegativeAnd
    (slot variable1)
    (slot variable2)
)

(deftemplate _or
    (slot name)
    (slot variable1)
    (slot variable2)
)

(deftemplate _orAndVar
    (slot orName)
    (slot variable)
)

(deftemplate _orOrVar
    (slot orName)
    (slot variable)
)

(deftemplate _orAndOr
    (slot orName1)
    (slot orName2)
)

(deftemplate _orOrOr
    (slot orName1)
    (slot orName2)
)

(deftemplate _and
    (slot name)
    (slot variable1)
    (slot variable2)
)

(deftemplate _andOrVar
    (slot andName)
    (slot variable)
)

(deftemplate _andAndVar
    (slot andName)
    (slot variable)
)

(deftemplate _andAndAnd
    (slot andName1)
    (slot andName2)
)

(deftemplate _andOrAnd
    (slot andName1)
    (slot andName2)
)

(deftemplate _imply
    (slot variable1)
    (slot variable2)
)

(defglobal ?*orNum1* = 0) ; counter for 'or' names
(defglobal ?*orNum2* = 1000) ; counter for 'or' names
(defglobal ?*andNum1* = 0) ; counter for 'and' names
(defglobal ?*andNum2* = 1000) ; counter for 'and' names

(deffacts identities
    (variable (name P) (negative 0))
    (variable (name Q) (negative 0))
    (variable (name R) (negative 0))
    (_and (name 99)(variable1 Q) (variable2 R))
    (_andOrVar (andName 99) (variable P))
)





; * the commutative laws: (P ∧ Q) ≡ (Q ∧ P) and (P ∨ Q) ≡ (Q ∨ P) 
; * the associative law: ((P ∧ Q) ∧ R) ≡ (P ∧ (Q ∧ R)) 
; * the associative law: ((P ∨ Q) ∨ R) ≡ (P ∨ (Q ∨ R))



(defrule orNaming
    ?out <- (_or (name nil))
=> 
    (bind ?*orNum1* (+ 1 ?*orNum1*))
    (modify ?out (name ?*orNum1*) )
)

(defrule andNaming
    ?out <- (_and (name nil))
=> 
    (bind ?*andNum1* (+ 1 ?*andNum1*))
    (modify ?out (name ?*andNum1*) )
)

; - the distributive law: P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
(defrule distributive1
    ?out1 <- (_and (name ?aName)(variable1 ?x) (variable2 ?y))
    ?out2 <- (_andOrVar (andName ?aName) (variable ?z))
=>
    (bind ?*orNum1* (+ 1 ?*orNum1*))
    (bind ?*orNum2* (+ 1 ?*orNum1*))
    (assert (_or (name ?*orNum1*)(variable1 ?z)(variable2 ?x)))
    (assert (_or (name ?*orNum2*)(variable1 ?z)(variable2 ?y)))
    (assert (_orAndOr (orName1 ?*orNum1*)(orName2 ?*orNum2*)))
    (retract ?out1)
    (retract ?out2)
    (printout t "Distributive : " ?z " OR (" ?x " AND " ?y") == (" ?z " OR " ?x") AND (" ?z " OR " ?y ")")
)

; - the distributive law: P ∧ (Q ∨ R) ≡ (P ∧ Q) ∨ (P ∧ R)
(defrule distributive2
    ?out1 <- (_or (name ?aName)(variable1 ?x) (variable2 ?y))
    ?out2 <- (_orAndVar (orName ?aName) (variable ?z))
=>
    (bind ?*andNum1* (+ 1 ?*andNum1*))
    (bind ?*andNum2* (+ 1 ?*andNum1*))
    (assert (_and (name ?*andNum1*)(variable1 ?z)(variable2 ?x)))
    (assert (_and (name ?*andNum2*)(variable1 ?z)(variable2 ?y)))
    (assert (_andOrAnd (andName1 ?*andNum1*)(andName2 ?*andNum2*)))
    (retract ?out1)
    (retract ?out2)
    (printout t "Distributive : " ?z " AND (" ?x " OR " ?y") == (" ?z " AND " ?x") OR (" ?z " AND " ?y ")")
)

; - de Morgan’s law: ¬ (P ∨ Q) ≡ (¬ P ∧ ¬Q)
(defrule deMorganOr
    ?out0 <- (_applyNegativeOr (variable1 ?x) (variable2 ?y))
    (_or (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative ?isN2))
    ?out3 <- (variable (name ?y) (negative ?isN3))
=> 
    (retract ?out0)
    (if (= ?isN2 1)
        then
            (modify ?out2 (negative 0))
        else
            (modify ?out2 (negative 1))
    )
    (if (= ?isN3 1)
        then
            (modify ?out3 (negative 0))

        else
            (modify ?out3 (negative 1))  
    )    
)

; - de Morgan’s law: ¬ (P ∧ Q) ≡ (¬ P ∨ ¬Q)
(defrule deMorganAnd
    ?out0 <- (_applyNegativeAnd (variable1 ?x) (variable2 ?y))
    (_and (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative ?isN2))
    ?out3 <- (variable (name ?y) (negative ?isN3))
=> 
    (retract ?out0)
    (if (= ?isN2 1)
        then
            (modify ?out2 (negative 0))
        else
            (modify ?out2 (negative 1))
    )
    (if (= ?isN3 1)
        then
            (modify ?out3 (negative 0))

        else
            (modify ?out3 (negative 1))
           
    )    
)

; - the contrapositive law: (P → Q) ≡ (¬ Q → ¬P)
(defrule contrapositive
    ?out1 <- (_imply (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative 0))
    ?out3 <- (variable (name ?y) (negative 0))
=> 
    (assert (_imply (variable1 ?y) (variable2 ?x)))
    (modify ?out2 (negative 1))
    (modify ?out3 (negative 1))
    (retract ?out1)
)

; (defrule commutative
;     ?out <- (_or (variable1 ?x) (variable2 ?y))
;     (variable (name ?x) (negative ?))
;     (variable (name ?y) (negative ?))
; =>
;     (assert (_or (variable1 ?y) (variable2 ?x)))
; )

; - implication rule: (P ∨ Q) ≡ (¬ P → Q)
(defrule implication
    ?out1 <- (_or (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative 0))
    (variable (name ?y) (negative 0))
=> 
    (assert (_imply (variable1 ?x) (variable2 ?y)))
    (modify ?out2 (negative 1))
    (retract ?out1)
)

; - double negative: ¬ (¬ P) ≡ P 
(defrule double-negative
    ?out <- (variable (name ?x) (negative ?isN))
    ?out2 <- (_applyNegativeVariable (variable ?x))
=> 
    (if (= ?isN 1)
        then
            (modify ?out (negative 0))
            (retract ?out2)
        else
            (modify ?out (negative 1))
            (retract ?out2)
    )
)