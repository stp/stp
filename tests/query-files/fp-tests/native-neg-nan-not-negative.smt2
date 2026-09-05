; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; fp.neg keeps a NaN a NaN (the payload sign bit flips, the value does
; not leave the NaN class), and fp.isNegative is false on every NaN. The
; classification operand is fp.neg over a symbol, so the native path keeps
; the classification (isNegative is one of the two the factory's
; sign-stripping rule deliberately leaves alone) and reads the flipped
; sign bit -- the NaN conjunct in BBclassifyFP must still veto it.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isNegative (fp.neg x)))
(check-sat)
(exit)
