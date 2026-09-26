; RUN: not %solver --SMTLIB2 %s 2>&1 | %OutputCheck %s
;
; Folding constant products must not open the door to a genuinely
; nonlinear one: neither operand here is concrete.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x y) 1.0))
; CHECK-L: multiplication requires an exact concrete coefficient
(check-sat)
