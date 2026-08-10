; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Narrowing under RTZ saturates to the largest finite value, never to
; infinity: a finite double cannot become an infinite float. Pins the
; mode-dependent overflow saturation inside the conversion's rounder.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (fp.isInfinite ((_ to_fp 8 24) RTZ x)))
(check-sat)
(exit)
