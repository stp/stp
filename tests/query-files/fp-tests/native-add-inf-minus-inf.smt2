; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Subtracting infinities is the invalid operation: infinity plus its own
; negation must be NaN, whichever infinity it is.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isInfinite x))
(assert (not (fp.isNaN (fp.add RNE x (fp.neg x)))))
(check-sat)
(exit)
