; RUN: %solver --exit-after-CNF %s | %OutputCheck %s

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun v0 () Bool )
(declare-fun v1 () Bool )
(declare-fun v2 () Bool )
(declare-fun v3 () Bool )
(declare-fun v4 () Bool )
(declare-fun v5 () Bool )

; The variables appear only in this expression, so
; they should be simplified out.
(assert (xor (xor (not v0) (not v1)) (xor (not v3) (not v2))))
(assert (xor v4 v5))

; CHECK-NEXT: ^sat
(check-sat)
(exit)


