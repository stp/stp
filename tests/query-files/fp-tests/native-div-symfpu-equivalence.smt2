; Compare the native divide circuit with an independent SymFPU encoding over
; every value of (3,4) and every rounding mode. The oracle divides the same
; dividend expressed as an FMA by a symbolic one against a symbolic minus
; zero -- the identity on every value, signed zeros included -- which keeps
; the oracle's dividend off the native packed path so its divide stays on
; SymFPU. Structural equality detects signed-zero disagreements; NaN
; payloads are deliberately ignored.
;
; RUN: %solver --bb.fp-native-all=false --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-div=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 2 SymFPU operations, 5 unpacks
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 4))
(declare-fun b () (_ FloatingPoint 3 4))
(declare-fun unit () (_ FloatingPoint 3 4))
(declare-fun minus-zero () (_ FloatingPoint 3 4))
(declare-fun rm () RoundingMode)
(declare-fun native-div () (_ FloatingPoint 3 4))
(declare-fun oracle-div () (_ FloatingPoint 3 4))
(define-fun one () (_ FloatingPoint 3 4) (fp #b0 #b011 #b000))

(assert (fp.leq one unit))
(assert (fp.leq unit one))
(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-div (fp.div rm a b)))
(assert (= oracle-div (fp.div rm (fp.fma RNE a unit minus-zero) b)))
(assert
  (not (or (= native-div oracle-div)
           (and (fp.isNaN native-div) (fp.isNaN oracle-div)))))
(check-sat)
(exit)
