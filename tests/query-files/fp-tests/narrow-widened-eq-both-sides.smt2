; RUN: %solver %s | %OutputCheck %s
;
; Both operands widened from float32: the equality compares the operands,
; which fp.lt of the same pair contradicts.
;
; CHECK: ^unsat
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) RNE y)))
(assert (fp.lt x y))
(check-sat)
(exit)
