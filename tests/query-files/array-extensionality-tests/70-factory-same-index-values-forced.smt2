; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Both sides overwrite the same index of the same base, so the equality
; forces exactly the written values equal. The simplifying factory folds
; this at construction into v = w; no witness machinery is involved.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun w () (_ BitVec 8))
(assert (= (store a i v) (store a i w)))
(assert (distinct v w))
(check-sat)
