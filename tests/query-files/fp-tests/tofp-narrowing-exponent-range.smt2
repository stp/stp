; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
;
; Float-to-float to_fp where the target's exponent RANGE shrinks even though
; the internal unpacked exponent width does not. The conversion used to take
; an unrounded fast path in those cases and return values outside the target
; format: overflows came back as NaNs, subnormals or zeros instead of
; saturating, and ties were never rounded at all. See issue #782; the fix is
; carried as patches/symfpu/.
;
; Each expected result was computed with exact rational arithmetic, and each
; is probed on its own so a failure names the row. The significand-only
; narrowing near the end is the control that the fix must not disturb: the
; unpacked exponent width shrinks there while the format's does not, which
; is the case that an over-broad version of the fix breaks.
;
(set-logic QF_FP)
(declare-fun z2_4 () (_ FloatingPoint 2 4))
(declare-fun z2_5 () (_ FloatingPoint 2 5))
(declare-fun z3_7 () (_ FloatingPoint 3 7))
(declare-fun z4_8 () (_ FloatingPoint 4 8))

; the tie that must round to even, not the odd neighbour
; CHECK: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b0000011)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0000010)))
(check-sat)
(pop 1)

; the smallest subnormal, converted into a narrower exponent range
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b0000001)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0000000)))
(check-sat)
(pop 1)

; a value past the target's range must saturate to infinity
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b0100100)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0101000)))
(check-sat)
(pop 1)

; and under RTZ it must saturate to the largest finite instead
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RTZ ((_ to_fp 3 4) #b0100100)))))
(assert (= z2_5 ((_ to_fp 2 5) #b0101000)))
(check-sat)
(pop 1)

; the same narrowing with a 3-bit target exponent
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z3_7 ((_ to_fp 3 7) RNE ((_ to_fp 4 4) #b10010001)))))
(assert (= z3_7 ((_ to_fp 3 7) #b1000001001)))
(check-sat)
(pop 1)

; a negative value past the range
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_5 ((_ to_fp 2 5) RNE ((_ to_fp 3 4) #b1100100)))))
(assert (= z2_5 ((_ to_fp 2 5) #b1101000)))
(check-sat)
(pop 1)

; narrowing only the significand, exponent range unchanged
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_4 ((_ to_fp 2 4) RNE ((_ to_fp 2 6) #b00000001)))))
(assert (= z2_4 ((_ to_fp 2 4) #b000000)))
(check-sat)
(pop 1)

; the same, negative
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z2_4 ((_ to_fp 2 4) RNE ((_ to_fp 2 6) #b10000001)))))
(assert (= z2_4 ((_ to_fp 2 4) #b100000)))
(check-sat)
(pop 1)

; a widening that must stay exact
; CHECK-NEXT: ^unsat
(push 1)
(assert (not (= z4_8 ((_ to_fp 4 8) RNE ((_ to_fp 2 5) #b0010101)))))
(assert (= z4_8 ((_ to_fp 4 8) #b001110101000)))
(check-sat)
(pop 1)

(exit)
