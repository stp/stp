; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The same for +oo: one Real, whichever +oo it is.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isInfinite x))
(assert (fp.isPositive x))
(assert (fp.isInfinite y))
(assert (fp.isPositive y))
(assert (not (= (fp.to_real x) (fp.to_real y))))
(check-sat)
