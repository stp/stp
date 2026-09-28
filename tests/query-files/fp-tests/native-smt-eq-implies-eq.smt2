; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The two equalities differ only at NaN and at the zeros, and in one
; direction only: for a non-NaN operand, x = y implies fp.eq x y (the
; converse fails at +0 = -0). So this formula is unsatisfiable. It ties the
; two native encodings (BBeqFP) to each other -- they share their bit
; equality but flip both corner cases, so a corner handled in the wrong kind
; shows up here as sat.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (= x y))
(assert (not (fp.eq x y)))
(check-sat)
(exit)
