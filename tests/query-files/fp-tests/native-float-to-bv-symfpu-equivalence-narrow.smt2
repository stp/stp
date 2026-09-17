; Compare the native fp.to_sbv circuit with an independent SymFPU encoding
; over every value of (2,5). The oracle converts the same float expressed
; as an addition of a symbolic minus zero -- the identity on every value,
; signed zeros included -- which with native arithmetic off keeps the
; oracle's conversion on the SymFPU path.
;
; Both arms index the same unspecified-value cell, because FpTotalise keys
; that cell on the float's canonical bits rather than on the node, so a
; disagreement about which inputs are even in range shows up here too.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-conv=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_BVFP)
(declare-fun a () (_ FloatingPoint 2 5))
(declare-fun minus-zero () (_ FloatingPoint 2 5))
(declare-fun rm () RoundingMode)
(declare-fun native-conv () (_ BitVec 3))
(declare-fun oracle-conv () (_ BitVec 3))

(assert (fp.isZero minus-zero))
(assert (fp.isNegative minus-zero))
(assert (= native-conv ((_ fp.to_sbv 3) rm a)))
(assert (= oracle-conv ((_ fp.to_sbv 3) rm (fp.add RNE a minus-zero))))
(assert (not (= native-conv oracle-conv)))
(check-sat)
(exit)
