; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; A strictly negative times a strictly positive value cannot be strictly
; positive: the product's sign is the XOR of the operand signs, so the
; result is negative, a negative zero (underflow), or negative infinity
; (overflow) -- never above +0. Exercises BBfpMul's sign wire against the
; native comparisons on both sides of it.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.lt x ((_ to_fp 8 24) #x00000000)))
(assert (fp.lt ((_ to_fp 8 24) #x00000000) y))
(assert (fp.gt (fp.mul RNE x y) ((_ to_fp 8 24) #x00000000)))
(check-sat)
(exit)
