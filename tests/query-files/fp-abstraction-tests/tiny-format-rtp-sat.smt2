; RUN: %solver --fp-abstraction=true --fp-abstraction-width=4 %s | %OutputCheck %s
;
; A tiny format under round-toward-positive, where every rule of the
; catalogue is exercised at its boundaries; the width floor is lowered so
; the abstraction engages on 7-bit floats.
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 4))
(declare-const y (_ FloatingPoint 3 4))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(assert (= (fp.mul RTP x y) ((_ to_fp 3 4) #b0100000)))
(check-sat)
