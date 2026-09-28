; Models with arrays in the incremental driver: values of scalars pinned
; through array constraints, across rounds.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(assert (= (select a #x05) #x40))
(push 1)
(assert (= x (select a #x05)))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \|x\| +#x40
(get-value (x))
(pop 1)
(push 1)
(assert (= x (bvadd (select a #x05) #x01)))
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#x41
(get-value (x))
(pop 1)
(exit)
