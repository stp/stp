; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; The native multiply must also be able to FIND models, not just refute:
; a product strictly greater than both (finite, above-one) operands exists,
; so the solver has to drive the whole unpack/multiply/round/pack circuit
; forwards to a witness.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun one () (_ FloatingPoint 8 24))
(assert (= one ((_ to_fp 8 24) #x3F800000)))
(assert (fp.lt one x))
(assert (fp.lt one y))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isInfinite y)))
(assert (fp.gt (fp.mul RNE x y) x))
(assert (fp.gt (fp.mul RNE x y) y))
(check-sat)
(exit)
