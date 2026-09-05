; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; For ordered (non-NaN) operands, fp.geq is exactly fp.gt-or-fp.eq, so the
; SAT solver proves the non-strict arm agrees with equality on every ordered
; binary32 pair -- including the zeros, where fp.eq supplies the (+0 = -0)
; case that the both-zero disjunct must match. (fp.eq was still SymFPU when
; this test was written; it is native now, which leaves the flag-off run as
; the cross-encoding check.) The --disable-simplifications run keeps
; fp.leq/fp.geq from being rewritten at parse (the factory mirrors leq onto
; geq), and the flag-off run proves the identity all-SymFPU.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (xor (fp.geq x y) (or (fp.gt x y) (fp.eq x y))))
(check-sat)
(exit)
