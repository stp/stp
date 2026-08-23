; Both the source and target exponent widths participate in the native
; float-to-float exponent envelope. Exercise each unsafe side and require the
; conversions to fall back to SymFPU while preserving the exact value 1.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 2 SymFPU operations
; CHECK: ^sat
;
(set-logic QF_FP)
(declare-fun wide () (_ FloatingPoint 33 2))
(declare-fun single () (_ FloatingPoint 8 24))
(declare-fun narrowed () (_ FloatingPoint 8 24))
(declare-fun widened () (_ FloatingPoint 33 2))
(define-fun one-wide () (_ FloatingPoint 33 2)
  (fp #b0 #b011111111111111111111111111111111 #b0))
(define-fun one-single () (_ FloatingPoint 8 24)
  (fp #b0 #b01111111 #b00000000000000000000000))

(assert (fp.leq one-wide wide))
(assert (fp.leq wide one-wide))
(assert (fp.leq one-single single))
(assert (fp.leq single one-single))
(assert (= narrowed ((_ to_fp 8 24) RNE wide)))
(assert (= widened ((_ to_fp 33 2) RNE single)))
(assert (fp.eq narrowed one-single))
(assert (fp.eq widened one-wide))
(check-sat)
(exit)
