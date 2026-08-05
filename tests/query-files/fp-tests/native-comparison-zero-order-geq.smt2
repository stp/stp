; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; Every zero is greater-or-equal to every other zero: +0 and -0 compare
; EQUAL despite different packed bits. In the native encoding (BBcompareFP)
; key(-0) < key(+0), so (fp.geq -0 +0) is the single pair the non-strict
; key comparison misorders; the both-zero DISJUNCT repairs exactly it --
; the mirror image of the strict case's conjunct, which
; native-comparison-zero-order.smt2 pins. If the disjunct regresses (or the
; strict conjunct is copied here by mistake), x = -0, y = +0 satisfies this
; formula.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (fp.isZero y))
(assert (not (fp.geq x y)))
(check-sat)
(exit)
