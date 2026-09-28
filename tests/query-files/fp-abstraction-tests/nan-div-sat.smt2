; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; 0/0 is NaN and nothing else makes a NaN from non-NaN operands but that
; and inf/inf: the class shell admits the witness, and the witness is
; model-checked against the exact divider.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (fp.isNaN (fp.div RNE x y)))
(assert (not (fp.isInfinite x)))
(check-sat)
