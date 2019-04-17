; (sent (symb P)(isNeg 0))  ≡ P
; (sent (symb P Q)(con ^)(isNeg 00)  ≡ (P^Q)
; (sent (symb P Q R)(con ^ ^)(isNeg 000)(brac 1)  ≡ (P^Q)^R

(deftemplate sent 
    (multislot symb (default -1))
    (multislot con (default -1))
    (multislot isNeg (default -1))
    (slot brac (default -1))
)

(deffacts identities
    (sent (symb P)(isNeg 0))
    (sent (symb Q)(isNeg 0))
)

(defrule _triggerAnd
    (sent (symb ?x)(con -1)(isNeg 0)(brac -1))
    (sent (symb ?y)(con -1)(isNeg 0)(brac -1))
    (not (test (= (str-compare ?x ?y) 0)))
    (not (sent (symb ?x ?y)(con AND)(isNeg 0 0)(brac -1)))
=>
    (assert (sent(symb ?x ?y)(con AND)(isNeg 0 0)(brac -1)))
    (format t "(%s AND %s)%n" ?x ?y)
) 

(defrule _triggerOr
    (sent (symb ?x)(con -1)(isNeg ?n1)(brac -1))
    (sent (symb ?y)(con -1)(isNeg ?n2)(brac -1))
    (not (test (= (str-compare ?x ?y) 0)))
    (or (test (= ?n1 0)) 
        (test (= ?n2 0)))
    (not (sent (symb ?x ?y)(con OR)(isNeg ?n1 ?n2)(brac -1)))
=>
    (assert (sent(symb ?x ?y)(con OR)(isNeg ?n1 ?n2)(brac -1)))
    (if (= ?n1 1)
        then
            (bind ?X (format nil "~%s" ?x))
        else
            (bind ?X ?x)
    )
    (if (= ?n2 1)
        then
            (bind ?Y (format nil "~%s" ?y))
        else
            (bind ?Y ?y)
    )
    (format t "(%s OR %s)%n" ?X ?Y)
) 

