; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Both zeros are 0.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (not (= (fp.to_real x) 0.0)))
(check-sat)
