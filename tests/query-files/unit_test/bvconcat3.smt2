; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2))
(declare-fun v1 () (_ BitVec 2))
(declare-fun v2 () (_ BitVec 2))
(declare-fun v3 () (_ BitVec 2))
(declare-fun v4 () (_ BitVec 2))
(declare-fun v5 () (_ BitVec 2))
(declare-fun v6 () (_ BitVec 2))
(declare-fun v7 () (_ BitVec 2))

(assert (= (concat v1 (concat v2 v3)) (concat (concat v1 v2) v3 ) ))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
