; RUN: %solver --SMTLIB2 --uf-ackermann on -s %s 2>&1 | %OutputCheck %s
;
; x is above 5 and y below 3, so the two applications can never be at the
; same point. The terms share nothing, so linear arithmetic alone cannot say
; so; the query's own unit bounds can, and the pair costs no constraint.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 5.0))
(assert (< y 3.0))
(assert (not (= (f x) (f y))))
; CHECK: 1 impossible, 0 constraints
; CHECK: ^sat
(check-sat)
