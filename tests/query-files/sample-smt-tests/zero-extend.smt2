; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 2))
(assert (xor (bvult ((_ sign_extend 1) x) (_ bv2 3)) (bvult x (_ bv2 2))))
; CHECK-NEXT: ^unsat
(check-sat)
