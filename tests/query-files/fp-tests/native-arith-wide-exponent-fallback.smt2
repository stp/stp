; Native arithmetic currently forms exponent bounds in a host unsigned. A
; legal format wider than that representation must stay on the SymFPU path.
; The two operands are numerically 1, so both results below are finite; the
; old unchecked native path incorrectly made this formula unsatisfiable.
;
; RUN: %solver --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 2 SymFPU operations, 2 unpacks
; CHECK: ^sat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 33 2))
(declare-fun b () (_ FloatingPoint 33 2))
(define-fun one () (_ FloatingPoint 33 2)
  (fp #b0 #b011111111111111111111111111111111 #b0))

(assert (fp.leq one a))
(assert (fp.leq a one))
(assert (fp.leq one b))
(assert (fp.leq b one))
(assert (not (fp.isInfinite (fp.add RNE a b))))
(assert (not (fp.isNaN (fp.add RNE a b))))
(assert (not (fp.isInfinite (fp.mul RNE a b))))
(assert (not (fp.isNaN (fp.mul RNE a b))))
(check-sat)
(exit)
