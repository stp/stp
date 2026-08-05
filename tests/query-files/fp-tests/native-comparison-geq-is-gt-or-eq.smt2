; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; For ordered (non-NaN) operands, fp.geq is exactly fp.gt-or-fp.eq. With
; all four ordering comparisons native, fp.eq is the remaining SymFPU
; encoding in this identity, so the SAT solver proves the native non-strict
; arm agrees with SymFPU's equality on every ordered binary32 pair --
; including the zeros, where fp.eq supplies the (+0 = -0) case that the
; both-zero disjunct must match. The --disable-simplifications run keeps
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
