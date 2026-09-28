; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The five value classes COVER the format: every packed operand is a NaN, an
; infinity, a zero, a subnormal or a normal, so no x escapes all five and
; this formula is unsatisfiable. Natively (BBclassifyFP) the classes are
; field tests on the exponent and significand, and the one easy to get wrong
; is isNormal: testing only "exponent nonzero" would admit infinities and
; NaNs, which passes this cover test but fails the disjointness one
; (native-classify-disjoint.smt2) -- the two files are complementary and both
; are needed.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (or (fp.isNaN x) (fp.isInfinite x) (fp.isZero x)
                 (fp.isSubnormal x) (fp.isNormal x))))
(check-sat)
(exit)
