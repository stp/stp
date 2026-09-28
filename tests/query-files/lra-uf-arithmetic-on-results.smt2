; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; An application is an ordinary Real term to the simplex, so arithmetic over
; it is refuted by the arithmetic rather than by anything about functions.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (< (+ (f x) 1.0) (f x)))
; CHECK: ^unsat
(check-sat)
