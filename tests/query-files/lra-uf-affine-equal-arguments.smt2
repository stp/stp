; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The two actuals are the same value written differently: (x + 2) - 1 and
; x + 1 are not the same term, so nothing catches them by identity, but they
; are equal for every x. Reading them as linear forms settles that, and the
; congruence between the two applications holds with no premise to discharge.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (not (= (f (- (+ x 2.0) 1.0)) (f (+ x 1.0)))))
; CHECK: ^unsat
(check-sat)
