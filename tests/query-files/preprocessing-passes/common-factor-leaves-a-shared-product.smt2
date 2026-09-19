; A product used somewhere else is built whatever this sum does, so taking a
; factor out of it would build the reduced product beside it rather than
; instead of it. Here (x*a) is also the subject of its own assertion, which
; leaves one product in the sum able to give x up -- and one is not sharing.
; RUN: %solver -s -d --flattening=1 --common-factor=1 %s 2>&1 | %OutputCheck %s
; CHECK: Multiplications saved:0
; CHECK: ^sat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(assert (= (bvadd (bvmul x a) (bvmul x b)) (_ bv100 8)))
(assert (bvugt (bvmul x a) (_ bv200 8)))
(assert (bvugt b (_ bv1 8)))
(check-sat)
(exit)
