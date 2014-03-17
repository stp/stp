; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 2))
(assert (xor (bvslt ((_ sign_extend 1) x) (_ bv0 3)) (bvslt x (_ bv0 2))))
; CHECK-NEXT: ^unsat
(check-sat)
