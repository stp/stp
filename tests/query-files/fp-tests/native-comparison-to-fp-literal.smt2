; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The usual spelling of a binary64 literal is to_fp's reinterpret form,
; which stays an unfolded three-child FP_TOFP term solver-wide (FP constant
; folding is deferred). The native-comparison gate resolves that form to
; the interned constant -- the same lookthrough RemoveUnconstrained uses --
; so these comparisons blast natively rather than falling back to SymFPU.
; x appears twice so RemoveUnconstrained cannot discharge the comparisons
; first; 1.3 < x < 2.0 is satisfiable, and the sat model is validated
; internally against SymFPU's constant evaluation.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(assert (fp.gt x ((_ to_fp 11 53) #x3FF4CCCCCCCCCCCD))) ; x > 1.3
(assert (fp.lt x ((_ to_fp 11 53) #x4000000000000000))) ; x < 2.0
(check-sat)
(exit)
