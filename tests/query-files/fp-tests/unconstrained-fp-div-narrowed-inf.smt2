; RUN: %solver -d %s | %OutputCheck %s
;
; An infinite numerator confines the narrowed quotient to {+oo, -oo, NaN}:
; reaching +oo from -oo takes a negative (finite or zero) divisor, which the
; recorded witness supplies for the model check.
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
