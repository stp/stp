; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\(
; CHECK-NEXT: \(fp #b0 #b01111110 #b00000000000000000000000\)
; Linear arithmetic over conversions: x + x = 1 makes x one half.
(set-option :produce-models true)
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= (+ (fp.to_real x) (fp.to_real x)) 1.0))
(check-sat)
(get-value (x))
