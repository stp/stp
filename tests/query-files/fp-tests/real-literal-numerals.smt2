; RUN: %solver %s | %OutputCheck %s
;
; Bare numerals as real constants: 1 is 1.0, 0 is +zero, and 16777217 --
; the 2^24 + 1 halfway case, spelled without a decimal point -- still
; splits the nearest modes.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
(assert (= a ((_ to_fp 8 24) RNE 1)))
(assert (= b ((_ to_fp 8 24) RNE 16777217)))
(assert (= c ((_ to_fp 8 24) RNA 16777217)))
(assert (or
  (distinct a ((_ to_fp 8 24) #x3f800000))
  (distinct a ((_ to_fp 8 24) RNE 1.0))
  (distinct b ((_ to_fp 8 24) #x4b800000))
  (distinct c ((_ to_fp 8 24) #x4b800001))
  (distinct ((_ to_fp 8 24) RTN 0) (_ +zero 8 24))))
; CHECK: ^unsat
(check-sat)
