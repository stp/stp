; RUN: %solver --array-equality --ackermanize %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Writes are accesses for the eager instantiation exactly as they are
; for the lazy checker (test 02): no explicit read anywhere, yet equal
; stores at equal indices force equal values. The write index has to be
; in the pointwise instantiation's index inventory for the equality to
; be observed at it.
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
