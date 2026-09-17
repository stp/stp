; Compare the native fused multiply-add with an independent SymFPU encoding
; over every value of (4,4) and every rounding mode. The oracle takes the
; same first operand expressed as an addition of a symbolic minus zero --
; the identity on every value, signed zeros included -- which with native
; arithmetic off keeps the oracle's FMA on the SymFPU path.
;
; Formats matter here more than anywhere else. (4,4) caught the datapath
; ordering a zero addend above a smaller nonzero product, and (4,4)-style
; wide significands caught the exponent datapath being too narrow for a
; leading-zero count taken over a frame four significands wide.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-fma=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 4 4))
(declare-fun b () (_ FloatingPoint 4 4))
(declare-fun c () (_ FloatingPoint 4 4))
(declare-fun minus-zero () (_ FloatingPoint 4 4))
(declare-fun rm () RoundingMode)
(declare-fun native-fma () (_ FloatingPoint 4 4))
(declare-fun oracle-fma () (_ FloatingPoint 4 4))

(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-fma (fp.fma rm a b c)))
(assert (= oracle-fma (fp.fma rm (fp.add RNE a minus-zero) b c)))
(assert (not (= native-fma oracle-fma)))
(check-sat)
(exit)
