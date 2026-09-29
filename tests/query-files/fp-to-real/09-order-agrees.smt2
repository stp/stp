; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; For finite floats, fp.lt and < on the Real values agree.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isInfinite y)))
(assert (fp.lt x y))
(assert (>= (fp.to_real x) (fp.to_real y)))
(check-sat)
