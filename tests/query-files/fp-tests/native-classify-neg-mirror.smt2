; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; Cross-encoding check that survives this migration: fp.neg is an FP
; OPERATION, so (fp.isPositive (fp.neg x)) fails the leaf gate and is built
; entirely by SymFPU, while (fp.isNegative x) is native (BBclassifyFP). The
; two are equal for every x -- NaN: both false, since neither sign predicate
; holds of a NaN; zeros: -0 is negative and its negation +0 is positive --
; so this formula is unsatisfiable. The classification predicates are native
; now and can no longer serve as the SymFPU anchor for each other; routing
; one side through an FP operation restores that. (The factory's peel rule
; for a negated operand deliberately skips the two sign predicates, so
; fp.neg really does survive to lowering here.)
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (xor (fp.isNegative x) (fp.isPositive (fp.neg x))))
(check-sat)
(exit)
