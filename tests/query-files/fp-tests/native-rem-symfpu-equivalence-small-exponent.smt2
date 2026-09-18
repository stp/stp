; Compare the native IEEE remainder with an independent SymFPU encoding over
; every value of (2,5). The oracle takes the same dividend expressed as an
; addition of a symbolic minus zero -- the identity on every value, signed
; zeros included -- which with native arithmetic off keeps the oracle on the
; SymFPU path.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-rem=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 2 5))
(declare-fun b () (_ FloatingPoint 2 5))
(declare-fun minus-zero () (_ FloatingPoint 2 5))
(declare-fun native-rem () (_ FloatingPoint 2 5))
(declare-fun oracle-rem () (_ FloatingPoint 2 5))

(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-rem (fp.rem a b)))
(assert (= oracle-rem (fp.rem (fp.add RNE a minus-zero) b)))
(assert (not (= native-rem oracle-rem)))
(check-sat)
(exit)
