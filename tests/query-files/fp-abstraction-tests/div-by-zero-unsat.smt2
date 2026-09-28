; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; Dividing a finite nonzero by a zero is an infinity of the product sign:
; shell rules of the divider.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.isNormal x))
(assert (fp.isZero y))
(assert (not (fp.isInfinite (fp.div RNE x y))))
(check-sat)
