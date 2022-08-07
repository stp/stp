; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 2))
(assert (= (bvor v0 v0) (_ bv0 2)))
(assert (= (bvor v1 (bvnot v1)) (_ bv3 2)))

; CHECK-NEXT: ^sat
(check-sat)
(exit)
