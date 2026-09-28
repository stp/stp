; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A Real-sorted term ite. The frontend names the value and states what the
; name means on each branch, so the simplex only ever sees linear terms.
; min(3, 5) = 3, so the constraint is unsatisfiable.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 3.0))
(assert (= y 5.0))
(assert (> (ite (< x y) x y) 4.0))
; CHECK: ^unsat
(check-sat)
