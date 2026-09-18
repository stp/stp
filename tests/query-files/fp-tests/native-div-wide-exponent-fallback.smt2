; The native divider forms exponent bounds in a host unsigned, and needs a
; wider envelope than the other native arithmetic because it normalises both
; significands before dividing. A legal format wider than that representation
; must stay on the SymFPU path. Both operands are numerically 1, so the
; quotient is finite.
;
; RUN: %solver --bb.fp-native-div=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 1 SymFPU operations, 2 unpacks
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
(assert (not (fp.isInfinite (fp.div RNE a b))))
(assert (not (fp.isNaN (fp.div RNE a b))))
(check-sat)
(exit)
