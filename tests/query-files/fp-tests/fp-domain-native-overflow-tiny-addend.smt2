; RUN: %solver -d %s | %OutputCheck %s
; RUN: %solver -d --bb.fp-native-domain=0 %s | %OutputCheck %s
; CHECK: ^sat
;
; The second addend is to_fp RTN of a binary128 value far above binary64's
; range, which is the largest finite binary64. Adding the smallest subnormal
; to it rounds to +oo under RTP, so the sum is not normal for that rounding
; mode. Computed in long double, the two sum to exactly the largest finite
; value, and the native domain used to take that as proof the sum was finite.
; Reduced from a fuzzer case.
(set-logic QF_FP)
(declare-fun r () RoundingMode)
(assert (distinct true (fp.isNormal (fp.add r (fp (_ bv0 1) (_ bv0 11) (_ bv1 52)) ((_ to_fp 11 53) RTN ((_ to_fp 15 113) #b01100001110110110100011010011001010111010110001010000111111010001111011100011010000000111111111101001101000011111111001001110101))))))
(check-sat)
(exit)
