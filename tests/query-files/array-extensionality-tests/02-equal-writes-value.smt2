; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Writes are treated as accesses -- no explicit read anywhere, yet
; equal stores at equal indices force equal values.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun e2 () (_ BitVec 2))
(assert (= (store a i e1) (store b j e2)))
(assert (= i j))
(assert (distinct e1 e2))
(check-sat)
