; RUN: %solver %s | %OutputCheck %s
;
; Both operands widened from float32: the conversions drop, and fp.gt with
; fp.leq of the same pair is unsatisfiable.
;
; CHECK: ^unsat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.gt ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) RNE y)))
(assert (fp.leq x y))
(check-sat)
(exit)
