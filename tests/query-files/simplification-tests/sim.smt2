; RUN: %solver --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () Bool )
(declare-fun v1 () Bool )
(declare-fun v2 () Bool )
(declare-fun v3 () Bool )

; not xor is iff.

(assert (not (xor v0 v1)))
(assert (not (xor v1 v2)))
(assert (not (xor v2 v3)))

; CHECK-NEXT: ^sat
(check-sat)
(exit)


