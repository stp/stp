; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; No zero is greater than another zero: +0 and -0 compare equal despite
; having different packed bits. In the native encoding (BBcompareFP) their
; sign-magnitude keys are adjacent, and (fp.gt +0 -0) is the single pair the
; key comparison misorders; the both-zero conjunct repairs exactly it. If
; that conjunct regresses, x = +0, y = -0 satisfies this formula.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (fp.isZero y))
(assert (fp.gt x y))
(check-sat)
(exit)
