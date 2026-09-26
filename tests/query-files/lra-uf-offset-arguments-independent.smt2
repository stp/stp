; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The other side of the same reasoning: two actuals that differ by a constant
; are never equal, so congruence relates nothing and the two results are free
; to take whatever values the arithmetic allows. Pruning the pair must not
; also assert that its results agree.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (f x) 0.0))
(assert (= (f (+ x 1.0)) 1.0))
; CHECK: ^sat
(check-sat)
