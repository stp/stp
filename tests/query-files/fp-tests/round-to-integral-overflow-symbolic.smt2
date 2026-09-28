; RUN: %solver %s | %OutputCheck %s
;
; In a format whose exponent range is narrower than its significand the
; top binade holds non-integers, and rounding one up is an integer the
; format has no finite for: 3.5 in (2, 3) under RNE is 4, beyond the
; largest finite 3. The result is the infinity of that sign, in the
; symbolic encoding as in the literal one -- SymFPU's roundToIntegral left
; an exponent one past the largest normal's, which packed to an infinity
; by accident and was no infinity to its own flags, so a query asking for
; one was unsat. Satisfiable, with x = 3.5.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 2 3))
(declare-const t (_ FloatingPoint 2 3))
(assert (= t (fp.roundToIntegral RNE x)))
(assert (fp.isInfinite t))
(assert (not (fp.isInfinite x)))
(check-sat)
