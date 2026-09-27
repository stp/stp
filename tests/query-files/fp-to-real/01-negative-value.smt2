; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\(
; CHECK-NEXT: \(fp #b1 #b10000000 #b01000000000000000000000\)
; A finite float whose Real value is -5/2 is -2.5.
(set-option :produce-models true)
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= (fp.to_real x) (- 2.5)))
(check-sat)
(get-value (x))
