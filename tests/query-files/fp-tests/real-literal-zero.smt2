; RUN: %solver %s | %OutputCheck %s
;
; "0.0" is +zero under every rounding mode -- SMT-LIB fixes the sign, and
; there is no "-0.0" literal to write (a decimal has no sign). '=' keeps
; +0 and -0 apart, so comparing against +zero checks the sign too.
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
(assert (= a ((_ to_fp 8 24) RNE 0.0)))
(assert (= b ((_ to_fp 8 24) RTN 0.0)))
(assert (= c ((_ to_fp 8 24) RTZ 0.0)))
(assert (or
  (distinct a (_ +zero 8 24))
  (distinct b (_ +zero 8 24))
  (distinct c (_ +zero 8 24))))
; CHECK: ^unsat
(check-sat)
