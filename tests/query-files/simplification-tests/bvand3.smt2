; RUN: %solver --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v1 () (_ BitVec 5))
(declare-fun v2 () (_ BitVec 5))
(declare-fun v3 () (_ BitVec 5))

; Identity is discovered.
(assert (=  (bvand (bvnot v1) (bvand v2 v3)) (bvand v3 (bvand (bvnot v1) v2))  ) )
(assert (=  (bvnot v1) v2 ))
; CHECK-NEXT: ^sat
(check-sat)

