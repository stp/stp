; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.neg is antitone: fp.lt(-x, -y) holds exactly when fp.lt(y, x), NaN
; (both orderings false) and the zeros (-(+0) = -0, and +-0 compare equal)
; included, so the two strict orderings below contradict. Both comparison
; operands are fp.neg over a symbol, so the native path keeps the
; comparison and negates the packed sign bit in place (BBTerm's FP_NEG
; arm); the third run proves the SymFPU path agrees.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.lt (fp.neg x) (fp.neg y)))
(assert (fp.lt x y))
(check-sat)
(exit)
