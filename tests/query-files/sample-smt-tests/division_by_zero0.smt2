; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
(set-logic QF_BV)
(set-info :source |
	Test new division/remainder by zero semantics.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)

;;;; division by zero evaluates to all ones.
(assert (= #b0 (bvudiv #b1 #b0)))

(check-sat)
(exit)
