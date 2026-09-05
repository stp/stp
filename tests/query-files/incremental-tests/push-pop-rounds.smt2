; BMC-style rounds: a growing common prefix, one pushed level per round that
; is popped again. Exercises the incremental driver's assumption retraction.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
(assert (bvult x y))
(push 1)
(assert (= y #x0000))
; nothing is below #x0000
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (= y #x0001))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt x y))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; the prefix alone is satisfiable
; CHECK-NEXT: ^sat
(check-sat)
; deepen the prefix and do another round
(assert (bvult y #x0004))
(push 1)
(assert (bvugt x #x0004))
; x < y < 4 contradicts x > 4
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x0001))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(exit)
