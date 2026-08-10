; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; Float-to-float to_fp where the target's exponent RANGE shrinks even though
; the internal unpacked exponent width does not. Those conversions used to
; take an unrounded fast path and return values outside the target format:
; overflows came back as NaNs, subnormals or zeros instead of saturating,
; and ties were never rounded at all. Issue #782; fixed by patches/symfpu/.
;
; Every expected result is computed with exact rational arithmetic, and each
; is probed on its own so a failure names the row. The first group are cases
; that were actually wrong -- picked by diffing the unpatched build against
; the oracle, so each one genuinely fails without the patch, across all five
; rounding modes and both signs.
;
; The controls at the end were always correct and must stay so. They are not
; padding: in (2,6) -> (2,4) the unpacked exponent width shrinks while the
; format's does not, which is exactly the case a too-broad version of this
; fix breaks by underflowing the extension width. That mistake was made once
; already, so it is pinned here.
;
(set-logic QF_FP)
(declare-fun z2_4 () (_ FloatingPoint 2 4))
(declare-fun z2_5 () (_ FloatingPoint 2 5))
(declare-fun z2_6 () (_ FloatingPoint 2 6))
(declare-fun z2_7 () (_ FloatingPoint 2 7))
(declare-fun z3_6 () (_ FloatingPoint 3 6))
(declare-fun z3_7 () (_ FloatingPoint 3 7))
(declare-fun z4_8 () (_ FloatingPoint 4 8))

; a subnormal tie must round to even, not to the odd neighbour
; CHECK: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b0000011)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0000010)))
(check-sat)
(pop 1)

; the same tie, negative
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b1000011)))))
(assert (= z2_5 ((_ to_fp 2 5) #b1000010)))
(check-sat)
(pop 1)

; a value past the target's range must saturate to infinity
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b0101001)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0110000)))
(check-sat)
(pop 1)

; and its negative
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b1101001)))))
(assert (= z2_5 ((_ to_fp 2 5) #b1110000)))
(check-sat)
(pop 1)

; round-to-zero saturates to the largest finite instead
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RTZ ((_ to_fp 3 4) #b0101000)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0101111)))
(check-sat)
(pop 1)

; round-toward-negative keeps a positive overflow finite
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RTN ((_ to_fp 3 4) #b0101000)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0101111)))
(check-sat)
(pop 1)

; round-toward-positive keeps a negative overflow finite
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RTP ((_ to_fp 3 4) #b1101000)))))
(assert (= z2_5 ((_ to_fp 2 5) #b1101111)))
(check-sat)
(pop 1)

; ties-to-away also saturates
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNA ((_ to_fp 3 4) #b0101001)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0110000)))
(check-sat)
(pop 1)

; a wider significand does not rescue the narrower exponent
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_6 ((_ to_fp 2 6) RNE ((_ to_fp 3 4) #b0101001)))))
(assert (= z2_6 ((_ to_fp 2 6) #b01100000)))
(check-sat)
(pop 1)

; nor does a wider source significand
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_7 ((_ to_fp 2 7) RNE ((_ to_fp 3 5) #b01010001)))))
(assert (= z2_7 ((_ to_fp 2 7) #b011000000)))
(check-sat)
(pop 1)

; the same narrowing into a 3-bit target exponent
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z3_7 ((_ to_fp 3 7) RNA ((_ to_fp 4 4) #b01011001)))))
(assert (= z3_7 ((_ to_fp 3 7) #b0111000000)))
(check-sat)
(pop 1)

; a subnormal there too
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z3_7 ((_ to_fp 3 7) RNA ((_ to_fp 4 4) #b00000001)))))
(assert (= z3_7 ((_ to_fp 3 7) #b0000000001)))
(check-sat)
(pop 1)

; control: narrowing only the significand, exponent range unchanged
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_4 ((_ to_fp 2 4) RNE ((_ to_fp 2 6) #b00000001)))))
(assert (= z2_4 ((_ to_fp 2 4) #b000000)))
(check-sat)
(pop 1)

; control: the same, negative
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_4 ((_ to_fp 2 4) RNE ((_ to_fp 2 6) #b10000001)))))
(assert (= z2_4 ((_ to_fp 2 4) #b100000)))
(check-sat)
(pop 1)

; control: the same under round-toward-positive
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_4 ((_ to_fp 2 4) RTP ((_ to_fp 2 6) #b00000001)))))
(assert (= z2_4 ((_ to_fp 2 4) #b000001)))
(check-sat)
(pop 1)

; control: a widening that must stay exact
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z4_8 ((_ to_fp 4 8) RNE ((_ to_fp 2 5) #b0010101)))))
(assert (= z4_8 ((_ to_fp 4 8) #b001110101000)))
(check-sat)
(pop 1)

; control: a same-exponent widening
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z3_6 ((_ to_fp 3 6) RNE ((_ to_fp 3 4) #b0100101)))))
(assert (= z3_6 ((_ to_fp 3 6) #b010010100)))
(check-sat)
(pop 1)

(exit)
