; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.eq identifies the two zeros: +0 and -0 have different packed bits but
; are IEEE-equal, so every pair of zeros satisfies fp.eq and this formula is
; unsatisfiable. The native encoding (BBeqFP) gets this from the both-zero
; disjunct that sits beside plain bit equality; drop it and x = -0, y = +0
; makes the formula sat. fp.isZero still lowers through SymFPU, so the two
; encodings are checked against each other.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (fp.isZero y))
(assert (not (fp.eq x y)))
(check-sat)
(exit)
