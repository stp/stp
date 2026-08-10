; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Needs upward propagation over the stores, the equality between them,
; then downward propagation -- the shape that shows why upward
; propagation is required for extensionality (also exercises the gate
; that keeps small-read-count queries on the refinement path).
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(declare-fun k () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun e2 () (_ BitVec 2))
(assert (= (store a i e1) (store b j e2)))
(assert (distinct k i))
(assert (distinct k j))
(assert (distinct (select a k) (select b k)))
(check-sat)
