; RUN: %solver --array-equality -d %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The first assertion makes p1 false, so the disequality's left operand is
; the constant array of -oo, and its witness read folds to that value. The
; value turned up twice, as the float constant and as the plain constant
; with its bits, which intern apart: the recovery took the two spellings for
; two values and reported the operand lost, and with the plain spelling
; alone it would have built a constant array whose default is not a float.
(set-logic QF_ABVFP)
(declare-fun a0 () (Array (_ BitVec 1) (_ FloatingPoint 3 3)))
(declare-fun a1 () (Array (_ BitVec 1) (_ FloatingPoint 3 3)))
(declare-fun i1 () (_ BitVec 1))
(declare-fun e0 () (_ FloatingPoint 3 3))
(declare-fun p1 () Bool)
(assert (= (ite p1 (fp #b0 #b011 #b00) e0) (ite p1 (fp #b1 #b010 #b00) (fp #b1 #b100 #b11))))
(assert (distinct (ite p1 a1 ((as const (Array (_ BitVec 1) (_ FloatingPoint 3 3))) (fp #b1 #b111 #b00))) (store a0 i1 e0)))
(check-sat)
