; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test a simple repeat
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 1))
(assert (not (= (concat v0 v0) ((_ repeat 2) v0))))
(check-sat)
(exit)
