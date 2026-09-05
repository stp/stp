; RUN: %solver %s | %OutputCheck %s
;
; The companion to roundtointegral-format-refused.smt2: only
; fp.roundToIntegral reaches symfpu's off-by-one guard, so only
; fp.roundToIntegral is refused at (_ FloatingPoint 4 5). The format itself
; is sound -- symfpu unpacks it, and every other operation builds -- so the
; refusal is per operation, as fp.rem's is, rather than taking the whole
; format away.
;
; Pinned so that "refuse the format" cannot pass for a fix.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 4 5))
(declare-const y (_ FloatingPoint 4 5))
(assert (fp.isNormal (fp.add RNE x y)))
(assert (fp.lt (fp.mul RNE x y) x))
(assert (fp.isPositive (fp.sqrt RNE (fp.abs x))))
(assert (fp.isNormal (fp.div RNE x y)))
(check-sat)
