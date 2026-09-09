; RUN: %solver %s | %OutputCheck %s
;
; The same rounding folded over a literal: the literal back-end aborted on
; SymFPU's postcondition here before the result was made an infinity on
; purpose. 3.75 in (2, 6) rounds up under RTP to 4, which is +oo there.
; CHECK: ^sat
(set-logic QF_FP)
(assert (= (fp.roundToIntegral RTP (fp #b0 #b10 #b11000)) (_ +oo 2 6)))
(assert (= (fp.roundToIntegral RTN (fp #b1 #b10 #b11000)) (_ -oo 2 6)))
(assert (= (fp.roundToIntegral RTN (fp #b0 #b10 #b11000)) (fp #b0 #b10 #b10000)))
(check-sat)
