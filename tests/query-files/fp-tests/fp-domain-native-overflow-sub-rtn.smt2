; RUN: %solver -d %s | %OutputCheck %s
; RUN: %solver -d --bb.fp-native-domain=0 %s | %OutputCheck %s
; CHECK: ^sat
;
; -max - 1 is -oo under RTN: any excess beyond the largest finite magnitude
; overflows toward the rounding direction. In long double the 1 is lost and
; the difference is exactly -max, which the native domain must not take as
; proof that the result is finite.
(set-logic QF_FP)
(declare-fun r () RoundingMode)
(declare-fun x () Float32)
(assert (= x (fp.sub r (fp #b1 #b11111110 #b11111111111111111111111) (fp #b0 #b01111111 #b00000000000000000000000))))
(assert (fp.isInfinite x))
(check-sat)
(exit)
