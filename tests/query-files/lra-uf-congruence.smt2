; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Congruence over a Real-sorted function. Its values are exact rationals the
; arithmetic holds, so nothing compares them as bit patterns: the relation is
; stated as equality constraints and decided with the rest of the arithmetic.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
; CHECK: ^unsat
(check-sat)
