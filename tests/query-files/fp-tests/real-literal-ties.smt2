; RUN: %solver %s | %OutputCheck %s
;
; 16777217 = 2^24 + 1 sits exactly halfway between the two nearest Float32
; values, so the nearest modes split: ties-to-even goes down to 2^24,
; ties-away goes up, and the directed modes do what their names say.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
(declare-fun d () (_ FloatingPoint 8 24))
(declare-fun e () (_ FloatingPoint 8 24))
(assert (= a ((_ to_fp 8 24) RNE 16777217.0)))
(assert (= b ((_ to_fp 8 24) RNA 16777217.0)))
(assert (= c ((_ to_fp 8 24) RTP 16777217.0)))
(assert (= d ((_ to_fp 8 24) RTN 16777217.0)))
(assert (= e ((_ to_fp 8 24) RTZ 16777217.0)))
(assert (or
  (distinct a ((_ to_fp 8 24) #x4b800000))
  (distinct b ((_ to_fp 8 24) #x4b800001))
  (distinct c ((_ to_fp 8 24) #x4b800001))
  (distinct d ((_ to_fp 8 24) #x4b800000))
  (distinct e ((_ to_fp 8 24) #x4b800000))))
; CHECK: ^unsat
(check-sat)
