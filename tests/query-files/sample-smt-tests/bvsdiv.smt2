; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test that signed division rounds to zero.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(assert (= (bvsdiv (_ bv3 2) (_ bv2 2)) (_ bv0 2)))
(check-sat)
(exit)
