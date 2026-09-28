; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; A positive dividend over positive divisors: y1 <= y2 gives x/y1 >= x/y2.
; Two binary64 dividers exactly; one monotonicity fact between the two
; records with the abstraction.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y1 (_ FloatingPoint 11 53))
(declare-const y2 (_ FloatingPoint 11 53))
(assert (fp.lt (_ +zero 11 53) x))
(assert (fp.lt (_ +zero 11 53) y1))
(assert (fp.leq y1 y2))
(assert (not (fp.isNaN (fp.div RNE x y1))))
(assert (not (fp.isNaN (fp.div RNE x y2))))
(assert (fp.lt (fp.div RNE x y1) (fp.div RNE x y2)))
(check-sat)
