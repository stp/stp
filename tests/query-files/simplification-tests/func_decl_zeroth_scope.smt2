; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_ABV)
(define-fun |a| () Bool true)
(assert |a|)
(push 1)
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(exit)
