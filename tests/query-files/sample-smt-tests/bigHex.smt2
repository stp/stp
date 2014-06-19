; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test that #x and #b literals are working. Allocation of big constants.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () (_ BitVec 2000))
(assert (= #b1111 #xf))
(assert (= v0 (bvnot (_ bv0 2000))))
(check-sat)
(exit)
