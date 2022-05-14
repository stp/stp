; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
(set-logic QF_BV)
(set-info :source |
	Test new division/remainder by zero semantics.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)

(declare-fun a () (_ BitVec 4))
(assert (not (= (bvsmod a #b0000) (bvurem a #b0000 ))))



(check-sat)
(exit)
