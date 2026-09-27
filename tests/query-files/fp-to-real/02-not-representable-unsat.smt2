; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; No finite float is exactly 1/3.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= (fp.to_real x) (/ 1 3)))
(check-sat)
