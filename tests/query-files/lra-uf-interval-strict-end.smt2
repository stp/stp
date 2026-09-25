; RUN: %solver --SMTLIB2 --uf-ackermann on -s %s 2>&1 | %OutputCheck %s
;
; The same ranges with one end open: x is strictly above 5 and y at most 5,
; so there is no point they share, and the pair is dropped.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 5.0))
(assert (<= y 5.0))
(assert (not (= (f x) (f y))))
; CHECK: 1 impossible, 0 constraints
; CHECK: ^sat
(check-sat)
