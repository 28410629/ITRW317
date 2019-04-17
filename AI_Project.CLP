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
    (slot name(default-dynamic (gensym*)))
    (slot variable1)
    (slot variable2)
    (slot commutative (default 0))
)

(deftemplate _orAndVar
    (slot orName)
    (slot variable)
)

(deftemplate _orOrVar
    (slot orName)
    (slot variable)
    (slot associative (default 0))
)

(deftemplate _orAndOr
    (slot orName1)
    (slot orName2)
)

(deftemplate _orAndImply
    (slot orName)
    (slot implyName)
)

(deftemplate _orOrOr
    (slot orName1)
    (slot orName2)
)

(deftemplate _and
    (slot name (default-dynamic (gensym*)))
    (slot variable1)
    (slot variable2)
    (slot commutative (default 0))
)

(deftemplate _andOrVar
    (slot andName)
    (slot variable)
)

(deftemplate _andAndVar
    (slot andName)
    (slot variable)
    (slot associative (default 0))
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
    (slot name(default-dynamic (gensym*)))
    (slot variable1)
    (slot variable2)
)

(defglobal ?*orNum1* = 1000) ; counter for 'or' names
(defglobal ?*orNum2* = 1500) ; counter for 'or' names
(defglobal ?*andNum1* = 2000) ; counter for 'and' names
(defglobal ?*andNum2* = 2500) ; counter for 'and' names
(defglobal ?*implyNum1* = 3000) ; counter for '->' names
(defglobal ?*implyNum2* = 3500) ; counter for '->' names

(deffacts identities
    ; the distributive law: P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
     (variable (name P) (negative 0))
     (variable (name Q) (negative 1))
     (variable (name R) (negative 0))
     (_and (name 99)(variable1 Q) (variable2 R))
     (_andOrVar (andName 99) (variable P))

    ; * the associative law: ((P ∧ Q) ∧ R) ≡ (P ∧ (Q ∧ R)) 
    (variable (name S) (negative 1))
    (variable (name T) (negative 1))
    (variable (name U) (negative 0))
    (_and (name 222)(variable1 S) (variable2 T))
    (_andAndVar (andName 222) (variable U))

    ; de Morgan’s law: ¬ (P ∧ Q) ≡ (¬ P ∨ ¬Q)
    ; (variable (name P) (negative 1))
    ; (variable (name Q) (negative 0))
    ; (_applyNegativeAnd (variable1 P) (variable2 Q))
    ; (_and (variable1 P) (variable2 Q))

    ; de Morgan’s law: ¬ (P ∨ Q) ≡ (¬ P ∧ ¬Q)
    ; (variable (name P) (negative 1))
    ; (variable (name Q) (negative 0))
    ; (_applyNegativeOr (variable1 P) (variable2 Q))
    ; (_or (variable1 P) (variable2 Q))
)

; * the commutative laws: (P ∧ Q) ≡ (Q ∧ P) 
(defrule commutativeAnd
    ?out <- (_and (variable1 ?x)(variable2 ?y)(commutative ?c&:(< ?c 2)))
=> 
    (bind ?c (+ 1 ?c))
    (modify ?out (variable1 ?y)(variable2 ?x)(commutative ?c))
)

; * the commutative laws: (P ∨ Q) ≡ (Q ∨ P) 
(defrule commutativeOr
    ?out <- (_or (variable1 ?x)(variable2 ?y)(commutative ?c&:(< ?c 2)))
=> 
    (bind ?c (+ 1 ?c))
    (modify ?out (variable1 ?y)(variable2 ?x)(commutative ?c))
)


(defrule implyOrChange1
    ?out <- (_orAndOr (orName1 ?x)(orName2 ?y))
    (_or (name ?x))
    (_imply (name ?y))
=> 
    (assert (_orAndImply (orName ?x)(implyName ?y)))
    (retract ?out)
)

(defrule implyOrChange2
    ?out <- (_orAndOr (orName1 ?x)(orName2 ?y))
    (_or (name ?y))
    (_imply (name ?x))
=> 
    (retract ?out)  
    (assert (_orAndImply (orName ?y)(implyName ?x)))
)

; * the associative law: ((P ∧ Q) ∧ R) ≡ (P ∧ (Q ∧ R)) 
(defrule associativeAnd
    ?out0 <- (_andAndVar (andName ?n)(variable ?z)(associative ?a&:(< ?a 2)))
    ?out1 <- (_and (name ?n)(variable1 ?x)(variable2 ?y))
    (variable (name ?x) (negative ?isN3))
    (variable (name ?y) (negative ?isN4))
    (variable (name ?z) (negative ?isN5))
=>
    (bind ?a (+ 1 ?a))
    (modify ?out0 (variable ?x)(associative ?a))
    (modify ?out1 (variable1 ?y)(variable2 ?z))
    (if (= ?isN3 1)
        then
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((~%s AND ~%s) AND ~%s) == (~%s AND (~%s AND ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((~%s AND ~%s) AND %s) == (~%s AND (~%s AND %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((~%s AND %s) AND ~%s) == (~%s AND (%s AND ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((~%s AND %s) AND %s) == (~%s AND (%s AND %s))%n" ?x ?y ?z ?x ?y ?z)
                )
            )   
        else
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((%s AND ~%s) AND ~%s) == (%s AND (~%s AND ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((%s AND ~%s) AND %s) == (%s AND (~%s AND %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((%s AND %s) AND ~%s) == (%s AND (%s AND ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((%s AND %s) AND %s) == (%s AND (%s AND %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
            )   
    ) 
)

; * the associative law: ((P ∨ Q) ∨ R) ≡ (P ∨ (Q ∨ R))
(defrule associativeOr
    ?out0 <- (_orOrVar (orName ?n)(variable ?z)(associative ?a&:(< ?a 2)))
    ?out1 <- (_or (name ?n)(variable1 ?x)(variable2 ?y))
    (variable (name ?x) (negative ?isN3))
    (variable (name ?y) (negative ?isN4))
    (variable (name ?z) (negative ?isN5))
=>
    (bind ?a (+ 1 ?a))
    (modify ?out0 (variable ?x)(associative ?a))
    (modify ?out1 (variable1 ?y)(variable2 ?z))
    (if (= ?isN3 1)
        then
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((~%s OR ~%s) OR ~%s) == (~%s OR (~%s OR ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((~%s OR ~%s) OR %s) == (~%s OR (~%s OR %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((~%s OR %s) OR ~%s) == (~%s OR (%s OR ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((~%s OR %s) OR %s) == (~%s OR (%s OR %s))%n" ?x ?y ?z ?x ?y ?z)
                )
            )   
        else
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((%s OR ~%s) OR ~%s) == (%s OR (~%s OR ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((%s OR ~%s) OR %s) == (%s OR (~%s OR %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Associative Law : ((%s OR %s) OR ~%s) == (%s OR (%s OR ~%s))%n" ?x ?y ?z ?x ?y ?z)
                        else
                            (format t "Associative Law : ((%s OR %s) OR %s) == (%s OR (%s OR %s))%n" ?x ?y ?z ?x ?y ?z)
                    )
            )   
    ) 
)


; - the distributive law: P ∨ (Q ∧ R) ≡ (P ∨ Q) ∧ (P ∨ R)
(defrule distributive1
    ?out1 <- (_and (name ?aName)(variable1 ?x) (variable2 ?y))
    ?out2 <- (_andOrVar (andName ?aName) (variable ?z))
    (variable (name ?x) (negative ?isN3))
    (variable (name ?y) (negative ?isN4))
    (variable (name ?z) (negative ?isN5))
=>
    (bind ?*orNum1* (+ 1 ?*orNum1*))
    (bind ?*orNum2* (+ 1 ?*orNum1*))
    (assert (_or (name ?*orNum1*)(variable1 ?z)(variable2 ?x)))
    (assert (_or (name ?*orNum2*)(variable1 ?z)(variable2 ?y)))
    (assert (_orAndOr (orName1 ?*orNum1*)(orName2 ?*orNum2*)))
    (if (= ?isN3 1)
        then
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s OR (~%s AND ~%s) == (~%s OR ~%s) AND (~%s OR ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s OR (~%s AND ~%s) == (%s OR ~%s) AND (%s OR ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s OR (~%s AND %s) == (~%s OR ~%s) AND (~%s OR %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s OR (~%s AND %s) == (%s OR ~%s) AND (%s OR %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                )
            )   
        else
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s OR (%s AND ~%s) == (~%s OR %s) AND (~%s OR ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s OR (%s AND ~%s) == (%s OR %s) AND (%s OR ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s OR (%s AND %s) == (~%s OR %s) AND (~%s OR %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s OR (%s AND %s) == (%s OR %s) AND (%s OR %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
            )   
    )  
    (retract ?out1)
    (retract ?out2)
)

; - the distributive law: P ∧ (Q ∨ R) ≡ (P ∧ Q) ∨ (P ∧ R)
(defrule distributive2
    ?out1 <- (_or (name ?aName)(variable1 ?x) (variable2 ?y))
    ?out2 <- (_orAndVar (orName ?aName) (variable ?z))
    (variable (name ?x) (negative ?isN3))
    (variable (name ?y) (negative ?isN4))
    (variable (name ?z) (negative ?isN5))
=>
    (bind ?*andNum1* (+ 1 ?*andNum1*))
    (bind ?*andNum2* (+ 1 ?*andNum1*))
    (assert (_and (name ?*andNum1*)(variable1 ?z)(variable2 ?x)))
    (assert (_and (name ?*andNum2*)(variable1 ?z)(variable2 ?y)))
    (assert (_andOrAnd (andName1 ?*andNum1*)(andName2 ?*andNum2*)))
    (if (= ?isN3 1)
        then
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s AND (~%s OR ~%s) == (~%s AND ~%s) OR (~%s AND ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s AND (~%s OR ~%s) == (%s AND ~%s) OR (%s AND ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s AND (~%s OR %s) == (~%s AND ~%s) OR (~%s AND %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s AND (~%s OR %s) == (%s AND ~%s) OR (%s AND %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                )
            )   
        else
            (if (= ?isN4 1)
                then
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s AND (%s OR ~%s) == (~%s AND %s) OR (~%s AND ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s AND (%s OR ~%s) == (%s AND %s) OR (%s AND ~%s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
                else
                    (if (= ?isN5 1)
                        then
                            (format t "Distributive : ~%s AND (%s OR %s) == (~%s AND %s) OR (~%s AND %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                        else
                            (format t "Distributive : %s AND (%s OR %s) == (%s AND %s) OR (%s AND %s)%n" ?z ?x ?y ?z ?x ?z ?y)
                    )
            )   
    ) 
    (retract ?out1)
    (retract ?out2)
)

; - de Morgan’s law: ¬ (P ∨ Q) ≡ (¬ P ∧ ¬Q)
(defrule deMorganOr
    ?out0 <- (_applyNegativeOr (variable1 ?x) (variable2 ?y))
    ?out1 <- (_or (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative ?isN2))
    ?out3 <- (variable (name ?y) (negative ?isN3))
=> 
    (retract ?out0)
    (retract ?out1)
    (assert (_and (variable1 ?x)(variable2 ?y)))
    (assert (_applyNegativeVariable (variable ?x)))
    (assert (_applyNegativeVariable (variable ?y)))
    (if (= ?isN2 1)
        then
            (if (= ?isN3 1)
                then
                    (format t "de Morgan's Law : ~(~%s OR ~%s) == (%s AND %s)%n" ?x ?y ?x ?y)
                else
                    (format t "de Morgan's Law : ~(~%s OR %s) == (%s AND ~%s)%n" ?x ?y ?x ?y)
            )   
        else
            (if (= ?isN3 1)
                then
                    (format t "de Morgan's Law : ~(%s OR ~%s) == (~%s AND %s)%n" ?x ?y ?x ?y)
                else
                    (format t "de Morgan's Law : ~(%s OR %s) == (~%s AND ~%s)%n" ?x ?y ?x ?y)
            )   
    )  
)

; - de Morgan’s law: ¬ (P ∧ Q) ≡ (¬ P ∨ ¬Q)
(defrule deMorganAnd
    ?out0 <- (_applyNegativeAnd (variable1 ?x) (variable2 ?y))
    ?out1 <- (_and (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative ?isN2))
    ?out3 <- (variable (name ?y) (negative ?isN3))
=> 
    (retract ?out0)
    (retract ?out1)
    (assert (_or (variable1 ?x)(variable2 ?y)))
    (assert (_applyNegativeVariable (variable ?x)))
    (assert (_applyNegativeVariable (variable ?y)))
    (if (= ?isN2 1)
        then
            (if (= ?isN3 1)
                then
                    (format t "de Morgan's Law : ~(~%s AND ~%s) == (%s OR %s)%n" ?x ?y ?x ?y)
                else
                    (format t "de Morgan's Law : ~(~%s AND %s) == (%s OR ~%s)%n" ?x ?y ?x ?y)
            )   
        else
            (if (= ?isN3 1)
                then
                    (format t "de Morgan's Law : ~(%s AND ~%s) == (~%s OR %s)%n" ?x ?y ?x ?y)
                else
                    (format t "de Morgan's Law : ~(%s AND %s) == (~%s OR ~%s)%n" ?x ?y ?x ?y)
            )   
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
    (format t "Contrapositive Law : (%s -> %s) == (~%s -> %s)%n" ?x ?y ?y ?x)
    (retract ?out1)
)

; - implication rule: (P ∨ Q) ≡ (¬ P → Q)
(defrule implication
    ?out1 <- (_or (name ?name) (variable1 ?x) (variable2 ?y))
    ?out2 <- (variable (name ?x) (negative 0))
    (variable (name ?y) (negative 0))
=> 
    (assert (_imply (name ?name)(variable1 ?x) (variable2 ?y)))
    (modify ?out2 (negative 1))
    (format t "Implication rule : (%s OR %s) == (~%s -> %s)%n" ?x ?y ?x ?y)
    (retract ?out1)
)

; - double negative: ¬ (¬ P) ≡ P 
(defrule double_negative_or_negation
    ?out <- (variable (name ?x) (negative ?isN))
    ?out2 <- (_applyNegativeVariable (variable ?x))
=> 
    (if (= ?isN 1)
        then
            (modify ?out (negative 0))
            (format t "Double negative : ~(~%s) == %s%n" ?x ?x)
            (retract ?out2)
        else
            (modify ?out (negative 1))
            (format t "Negation : ~(%s) == ~%s%n" ?x ?x)
            (retract ?out2)
    )
)

; (defrule commutative
;     ?out <- (_or (variable1 ?x) (variable2 ?y))
;     (variable (name ?x) (negative ?))
;     (variable (name ?y) (negative ?))
; =>
;     (assert (_or (variable1 ?y) (variable2 ?x)))
; )