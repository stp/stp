; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Infinity times a finite nonzero value is infinite (the sign may flip but
; the class cannot): with y neither NaN nor zero, the product of an infinite
; x is infinite, so demanding it finite is unsatisfiable. With the native
; arithmetic flag the multiply blasts through BBfpMul's special-case muxing;
; the third run is the SymFPU path agreeing.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isInfinite x))
(assert (not (fp.isNaN y)))
(assert (not (fp.isZero y)))
(assert (not (fp.isInfinite (fp.mul RNE x y))))
(check-sat)
(exit)
