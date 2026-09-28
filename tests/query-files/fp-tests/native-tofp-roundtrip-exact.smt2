; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Widening is exact and narrowing an exactly-representable value is exact,
; so converting a float up and back down returns it: fp.eq-equal for every
; non-NaN operand, whatever the rounding modes. Exercises both directions
; of the native conversion around a single symbol.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.eq ((_ to_fp 8 24) RTZ ((_ to_fp 11 53) RNE x)) x)))
(check-sat)
(exit)
