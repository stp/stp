; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A NaN is neither negative nor positive: its sign bit is meaningless, and
; the SAT solver is free to pick either value for it (and any payload), so
; this formula is unsatisfiable. Natively (BBclassifyFP) that is the not-NaN
; conjunct in both sign predicates; encode isNegative as the bare sign bit
; and a NaN with the sign set satisfies this.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (or (fp.isNegative x) (fp.isPositive x)))
(check-sat)
(exit)
