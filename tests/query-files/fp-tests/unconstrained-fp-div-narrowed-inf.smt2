; RUN: %solver -d %s | %OutputCheck %s
;
; An infinite numerator confines the quotient to {+oo, -oo, NaN}; +oo from
; -oo takes a negative divisor, which the witness supplies for -d.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (fp.isInfinite x))
(assert (fp.isNegative x))
(assert (= ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)) (_ +oo 8 24)))
(check-sat)
(exit)
