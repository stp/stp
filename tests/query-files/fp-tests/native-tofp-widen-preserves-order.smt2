; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Widening embeds the source values exactly, so it preserves the strict
; order: the narrow and wide comparisons must agree on every pair. This is
; the shape the fmcad12 benchmarks use everywhere -- float32 symbols
; widened to float64 before comparing.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (distinct (fp.lt x y)
                  (fp.lt ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) RNE y))))
(check-sat)
(exit)
