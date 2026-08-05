; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.eq is IEEE equality, so a NaN operand -- on either side, with ANY
; payload the SAT solver can pick -- makes it false, and this formula is
; unsatisfiable. In the native encoding (BBeqFP) that is the pair of
; not-NaN conjuncts, and NaN is recognised by its exponent and significand
; fields rather than a canonical bit pattern; a payload-sensitive test, or a
; not-NaN conjunct dropped from one side, makes this sat. fp.isNaN still
; lowers through SymFPU, and the third run proves that path agrees.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun w () (_ FloatingPoint 8 24))
(assert (or (and (fp.eq x y) (fp.isNaN x))
            (and (fp.eq z w) (fp.isNaN w))))
(check-sat)
(exit)
