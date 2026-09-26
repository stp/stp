; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The other direction, which a congruence relation stated too strongly would
; get wrong: distinct arguments put no constraint on the results at all.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (= x y)))
(assert (not (= (f x) (f y))))
; CHECK: ^sat
(check-sat)
