; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; fp.to_real of NaN is unspecified, but it is a function: every NaN of a
; format converts to the same Real.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isNaN y))
(assert (not (= (fp.to_real x) (fp.to_real y))))
(check-sat)
