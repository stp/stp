; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Distinct bases stay with the witness machinery: the writes force the
; arrays to agree everywhere except the overwritten index, so a model
; must place the differing cell exactly there.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(assert (= (store a i v) (store b i v)))
(assert (distinct (select a j) (select b j)))
(check-sat)
