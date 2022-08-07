; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun x () (_ BitVec 15))
(declare-fun y () (_ BitVec 5))

; Check that unconstrained elimination through >'s works.

(assert (bvsgt x (concat (_ bv0 10) y)) )
; CHECK-NEXT: ^sat
(check-sat)
(exit)
