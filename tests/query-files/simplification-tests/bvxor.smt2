; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2))

(assert (bvule (bvxor v0 (_ bv0 2)) v0))



; CHECK-NEXT: ^sat
(check-sat)
(exit)

