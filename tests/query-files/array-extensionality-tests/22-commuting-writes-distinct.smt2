; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Writes at provably distinct indices (offsets from one pointer)
; commute, so the swapped chains denote the same array.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun i () (_ BitVec 32))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (distinct (store (store a i x) (bvadd i (_ bv1 32)) y)
                  (store (store a (bvadd i (_ bv1 32)) y) i x)))
(check-sat)
