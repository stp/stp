; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
	Regression test for an unsound bvsmod constant-bit propagation rule.
	The propagator concluded x smod x = 0 from pointer-equal operand
	FixedBits, but NodeDomainAnalysis hands every unknown operand of a
	width the same placeholder object, so the two distinct operands here
	were folded to zero and the formula wrongly reported unsat.
	Satisfiable, e.g. v = 3: bvsmod(3, 8) = 3 >=s 1.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v () (_ BitVec 16))
(assert (not (bvslt (bvsmod v (bvshl (_ bv1 16) v)) (_ bv1 16))))
(check-sat)
(exit)
