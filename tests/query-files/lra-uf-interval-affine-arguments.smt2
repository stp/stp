; RUN: %solver --SMTLIB2 --uf-ackermann on -s %s 2>&1 | %OutputCheck %s
;
; The bounds carry through the arithmetic on the actuals: x + 10 ranges over
; [10, infinity) and y over (-infinity, 5], which do not meet.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 0.0))
(assert (<= y 5.0))
(assert (not (= (f (+ x 10.0)) (f y))))
; CHECK: 1 impossible, 0 constraints
; CHECK: ^sat
(check-sat)
