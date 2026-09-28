; RUN: %solver %s | %OutputCheck %s
;
; declare-const with a floating-point or RoundingMode sort must bind a
; usable symbol. Regression test: the const_decl action forgot to set the
; format widths, so the symbol typed as a Boolean and every later use was
; a syntax error (declare-fun always worked).
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 5))
(declare-const y Float32
)
(declare-const r RoundingMode)
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (fp.eq (fp.add r x x) (fp.add r x x)))
; CHECK: ^sat
(check-sat)
