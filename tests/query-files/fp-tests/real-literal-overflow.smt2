; RUN: %solver %s | %OutputCheck %s
;
; 65520 is above the largest Float16 (65504) but below 2^16, i.e. in
; overflow territory, where IEEE-754 is mode-specific: the nearest modes
; and the away-side directed mode give infinity, while RTZ and the
; toward-side directed mode stop at the largest finite value. Rounding a
; real can never produce NaN, and a positive literal can never reach -oo.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 5 11))
(declare-fun b () (_ FloatingPoint 5 11))
(declare-fun c () (_ FloatingPoint 5 11))
(declare-fun d () (_ FloatingPoint 5 11))
(declare-fun e () (_ FloatingPoint 5 11))
(assert (= a ((_ to_fp 5 11) RNE 65520.0)))
(assert (= b ((_ to_fp 5 11) RNA 65520.0)))
(assert (= c ((_ to_fp 5 11) RTP 65520.0)))
(assert (= d ((_ to_fp 5 11) RTN 65520.0)))
(assert (= e ((_ to_fp 5 11) RTZ 65520.0)))
(assert (or
  (distinct a (_ +oo 5 11))
  (distinct b (_ +oo 5 11))
  (distinct c (_ +oo 5 11))
  (distinct d (fp #b0 #b11110 #b1111111111))
  (distinct e (fp #b0 #b11110 #b1111111111))))
; CHECK: ^unsat
(check-sat)
