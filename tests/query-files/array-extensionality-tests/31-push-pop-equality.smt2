; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; An equality asserted under a pushed scope: unsat while it is in
; force, sat again after the pop. The record survives the pop in the
; persistent registry and its witness bundle is re-conjoined into the
; middle solve, which must not flip the verdict -- the fresh witness
; symbols are otherwise unconstrained. Re-asserting the equality
; reuses the record and turns the verdict back.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(assert (distinct (select a #b00) (select b #b00)))
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
