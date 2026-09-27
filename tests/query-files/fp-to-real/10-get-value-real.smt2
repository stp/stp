; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\(
; CHECK-NEXT: \(/ 3 2\)
; A Real defined through fp.to_real reads back exactly.
(set-option :produce-models true)
(set-logic QF_FPLRA)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun r () Real)
(assert (= x (fp #b0 #b01111111 #b10000000000000000000000)))
(assert (= r (fp.to_real x)))
(check-sat)
(get-value (r))
