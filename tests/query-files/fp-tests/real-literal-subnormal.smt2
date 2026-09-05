; RUN: %solver %s | %OutputCheck %s
;
; The subnormal end of Float16. 2^-24 is exactly the smallest subnormal.
; 2^-25 is exactly half of it -- a tie between zero and the smallest
; subnormal -- so ties-to-even underflows to +zero, ties-away and RTP round
; up to the subnormal, and the downward modes underflow to +zero (the
; result of rounding a positive value down to nothing is +zero, not -zero).
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 5 11))
(declare-fun b () (_ FloatingPoint 5 11))
(declare-fun c () (_ FloatingPoint 5 11))
(declare-fun d () (_ FloatingPoint 5 11))
(declare-fun e () (_ FloatingPoint 5 11))
(declare-fun f () (_ FloatingPoint 5 11))
(assert (= a ((_ to_fp 5 11) RNE 0.000000059604644775390625)))
(assert (= b ((_ to_fp 5 11) RNE 0.0000000298023223876953125)))
(assert (= c ((_ to_fp 5 11) RNA 0.0000000298023223876953125)))
(assert (= d ((_ to_fp 5 11) RTP 0.0000000298023223876953125)))
(assert (= e ((_ to_fp 5 11) RTN 0.0000000298023223876953125)))
(assert (= f ((_ to_fp 5 11) RTZ 0.0000000298023223876953125)))
(assert (or
  (distinct a (fp #b0 #b00000 #b0000000001))
  (distinct b (_ +zero 5 11))
  (distinct c (fp #b0 #b00000 #b0000000001))
  (distinct d (fp #b0 #b00000 #b0000000001))
  (distinct e (_ +zero 5 11))
  (distinct f (_ +zero 5 11))))
; CHECK: ^unsat
(check-sat)
