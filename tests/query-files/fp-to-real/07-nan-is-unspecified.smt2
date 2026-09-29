; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; ... and that Real is any Real: here 3/7, which no float is.
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (fp.to_real x) (/ 3 7)))
(check-sat)
