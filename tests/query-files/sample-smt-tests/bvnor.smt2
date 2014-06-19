; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test bvnor nesting.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 1))
(assert (= (_ bv0 1) ((_ extract 1 1) (bvnor (_ bv0 2) (bvnor (_ bv2 2) (concat (_ bv0 1) v0))))))
(check-sat)
(exit)
