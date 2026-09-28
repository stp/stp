; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Equal actuals reached through a coefficient rather than through an addend:
; 2 * x and x + x collect to the same linear form, so the two applications are
; congruent whatever x is.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (not (= (f (* 2.0 x)) (f (+ x x)))))
; CHECK: ^unsat
(check-sat)
