; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.gt(-x, x) is satisfiable exactly by the strictly negative x (for NaN
; both orderings are false, and for the zeros -x and x compare equal), so
; this checks the native path can also find models through a surviving
; fp.neg operand, not just refute.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.gt (fp.neg x) x))
(check-sat)
(exit)
