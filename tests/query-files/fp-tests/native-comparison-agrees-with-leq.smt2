; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; For ordered (non-NaN) operands, fp.gt is exactly the negation of fp.leq.
; fp.gt over symbols blasts natively (BBcompareFP) while fp.leq is not
; migrated and lowers through SymFPU, so the SAT solver proves the native
; and SymFPU encodings agree on every ordered binary32 pair -- +/-0,
; infinities and subnormals included. (NaN operands, where gt and leq are
; both false and the identity does not hold, are excluded here and covered
; by native-comparison-nan-never-gt.smt2.)
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
