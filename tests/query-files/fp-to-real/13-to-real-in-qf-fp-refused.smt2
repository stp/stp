; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK: Real
; QF_FP has no Real sort: a Real declaration there is refused.
(set-logic QF_FP)
(declare-fun r () Real)
(check-sat)
