; RUN: %solver -d %s | %OutputCheck %s
;
; A zero numerator confines the narrowed quotient to {+0, -0, NaN}, with the
; sign following the divisor's free sign: forcing the quotient to +0 from a
; NEGATIVE zero numerator is satisfiable (divisor of matching sign), and the
; model check reconstructs that divisor. The (= q +zero) spelling
; distinguishes the zero signs, unlike fp.eq.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (fp.isZero x))
(assert (fp.isNegative x))
(assert (= ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)) (_ +zero 8 24)))
(check-sat)
(exit)
