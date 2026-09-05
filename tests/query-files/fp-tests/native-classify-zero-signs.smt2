; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A zero is signed: -0 is negative and +0 is positive, exactly one of the
; two, so this formula is unsatisfiable. It pins the corner opposite to
; native-classify-nan-sign.smt2 -- the sign predicates must ignore the sign
; bit for NaN but honour it for zero. An isNegative that excluded zeros (a
; natural reading of "negative") makes -0 satisfy neither and this sat.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (not (xor (fp.isNegative x) (fp.isPositive x))))
(check-sat)
(exit)
