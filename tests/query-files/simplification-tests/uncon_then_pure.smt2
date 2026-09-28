; RUN: %solver --pure-literals=1 --exit-after-CNF %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A disjunction whose every branch is unconstrained, run with pure-literal
; detection on: between them the two passes have to settle it, because with
; --exit-after-CNF an answer only comes back if nothing was left to solve.
; Converted from uncon_then_pure.smt.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(declare-fun m () (_ BitVec 3))
(declare-fun p () (_ BitVec 3))
(assert (or (bvslt x y)
            (or (= (bvmul p m) (_ bv3 3))
                (= (bvadd p m) (_ bv3 3)))))
(check-sat)
(exit)
