; RUN: %solver --bb.fp-native-arith=true --disable-equality %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Halving the smallest positive subnormal under RTP rounds back UP to that
; same subnormal: the exact product is below every representable positive
; value, and rounding toward positive infinity may not cross zero. This
; pins the interaction the hand-written circuit gets wrong most easily --
; the sticky bits surviving the subnormal right shift and still driving the
; rounding increment. --disable-equality keeps the pins as constraints so
; the circuit (not constant folding) decides the first run.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x ((_ to_fp 8 24) #x00000001)))
(assert (= y ((_ to_fp 8 24) #x3F000000)))
(assert (not (fp.eq (fp.mul RTP x y) x)))
(check-sat)
(exit)
