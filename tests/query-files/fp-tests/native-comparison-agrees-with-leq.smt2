; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; For ordered (non-NaN) operands, fp.gt is exactly the negation of fp.leq.
; Both blast natively (BBcompareFP) with the flag on -- gt through the
; strict arm with the both-zero conjunct, leq through the non-strict arm
; with the both-zero disjunct -- so the SAT solver proves the two arms are
; complementary on every ordered binary32 pair, +/-0, infinities and
; subnormals included; the flag-off run proves the same identity all-SymFPU.
; (NaN operands, where gt and leq are both false and the identity does not
; hold, are excluded here and covered by
; native-comparison-nan-never-gt.smt2.)
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (xor (fp.gt x y) (not (fp.leq x y))))
(check-sat)
(exit)
