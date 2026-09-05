; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Exact cancellation gives the mode-dependent zero: x + (-x) is -0 under
; RTN and +0 under every other mode, so under RTN its fp.isNegative holds
; for every finite x. This pins the one place fp.add's result sign is not
; simply inherited from the larger operand.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isNegative (fp.add RTN x (fp.neg x)))))
(check-sat)
(exit)
