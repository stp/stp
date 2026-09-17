; Compare the native fp.roundToIntegral circuit with an independent SymFPU
; encoding over every value of (3,4) and every rounding mode. The oracle
; takes the same operand expressed as an FMA by a symbolic one against a
; symbolic minus zero -- the identity on every value, signed zeros included
; -- which keeps the oracle off the native packed path.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-round=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 4))
(declare-fun unit () (_ FloatingPoint 3 4))
(declare-fun minus-zero () (_ FloatingPoint 3 4))
(declare-fun rm () RoundingMode)
(declare-fun native-round () (_ FloatingPoint 3 4))
(declare-fun oracle-round () (_ FloatingPoint 3 4))
(define-fun one () (_ FloatingPoint 3 4) (fp #b0 #b011 #b000))

(assert (fp.leq one unit))
(assert (fp.leq unit one))
(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-round (fp.roundToIntegral rm a)))
(assert (= oracle-round (fp.roundToIntegral rm (fp.fma RNE a unit minus-zero))))
(assert (not (= native-round oracle-round)))
(check-sat)
(exit)
