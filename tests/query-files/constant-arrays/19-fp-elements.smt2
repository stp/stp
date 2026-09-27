; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Floating-point elements: every cell of the array is the float.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 4) (_ FloatingPoint 5 11)))
(declare-fun i () (_ BitVec 4))
(assert (= a ((as const (Array (_ BitVec 4) (_ FloatingPoint 5 11))) ((_ to_fp 5 11) RNE 1.5))))
(assert (not (fp.eq (select a i) ((_ to_fp 5 11) RNE 1.5))))
(check-sat)
