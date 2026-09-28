; RUN: %solver %s | %OutputCheck %s
;
; The addend pushes an already-overflowing product's exponent up by the
; carry the invariant did not allow for; round-to-nearest-even overflows to
; minus infinity.
; CHECK: ^sat
(set-logic QF_FP)
(assert (= (fp.fma RNE (fp #b1 #b110 #b11111111) (fp #b0 #b110 #b11111110) (fp #b1 #b101 #b00000001)) (_ -oo 3 9)))
(check-sat)
