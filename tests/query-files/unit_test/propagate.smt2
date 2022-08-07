; RUN: %solver --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

(declare-fun v0 () (_ BitVec 20))
(declare-fun v1 () (_ BitVec 20))

; Needs to realise that you can take the inverse of bvneg, or bvnot.
(assert (= (bvnot v0) (bvneg v1) ))
(assert (not (= v0 v1)))


(declare-fun v2 () (_ BitVec 20))
(declare-fun v3 () (_ BitVec  20))
(assert (= (bvmul (_ bv05 20 ) (bvnot v2)) (bvashr v3 v3) ))
;(assert (= v2 v3))



; CHECK-NEXT: ^sat
(check-sat)
(exit)

