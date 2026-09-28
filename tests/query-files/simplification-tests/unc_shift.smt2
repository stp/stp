; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Every shift here has unconstrained operands, so the unconstrained-variable
; pass has to dispose of all three before the SAT solver is reached: with
; --exit-after-CNF an answer only comes back if nothing was left to solve.
; Converted from unc_shift.smt.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(declare-fun w () (_ BitVec 3))
(declare-fun z () (_ BitVec 3))
(declare-fun q () (_ BitVec 3))
(declare-fun r () (_ BitVec 3))
(assert (= (bvshl x y) (_ bv4 3)))
(assert (= (bvashr w z) (_ bv4 3)))
(assert (= (bvshl q r) (_ bv4 3)))
(check-sat)
(exit)
