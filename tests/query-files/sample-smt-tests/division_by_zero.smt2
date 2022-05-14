; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
	Test new division/remainder by zero semantics. v2.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

;;;; division by zero evaluates to all ones.
(assert (= #b1 (bvudiv #b0 #b0)))
(assert (= #b1 (bvudiv #b1 #b0)))
(assert (= #b11 (bvudiv #b11 #b00)))

(declare-fun a () (_ BitVec 2))
(assert (= #b11 (bvudiv #b00 a)))
(assert (= #b11 (bvudiv a a)))

;;;;; remainder by zero evaluates to the first operand.
(assert (= #b0 (bvurem #b0 #b0)))
(assert (= #b1 (bvurem #b1 #b0)))
(assert (= #b11 (bvudiv #b11 #b00)))

;;;;; bvsdiv by zero evaluates to first operand if it's positive, otherwise 1.
(assert (= #b1 (bvsdiv #b0 #b0)))
(assert (= #b1 (bvsdiv #b1 #b0)))
(assert (= #b01 (bvsdiv #b11 #b00)))

;;;;; bvsrem by zero evaluates to the first operand.
(assert (= #b0 (bvsrem #b0 #b0)))
(assert (= #b1 (bvsrem #b1 #b0)))
(assert (= #b11 (bvsrem #b11 #b00)))
(assert (= #b01 (bvsrem #b01 #b00)))

;;;;; bvsmod by zero
(assert (= #b0 (bvsmod #b0 #b0)))
(assert (= #b1 (bvsmod #b1 #b0)))
(assert (= #b00 (bvsmod #b00 #b00)))
(assert (= #b01 (bvsmod #b01 #b00)))
(assert (= #b10 (bvsmod #b10 #b00)))
(assert (= #b11 (bvsmod #b11 #b00)))


(check-sat)
(exit)
