; RUN: %solver -d %s | %OutputCheck %s
;
; A division by an unconstrained float64 divisor, narrowed back to float32,
; reaches every float32 value: the whole quotient becomes a fresh variable
; and the divider circuit is never built. -d checks the constructed model
; against this input, evaluating the division at u's reconstructed value.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(assert (= ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)) ((_ to_fp 8 24) #x40400000)))
(check-sat)
(exit)
