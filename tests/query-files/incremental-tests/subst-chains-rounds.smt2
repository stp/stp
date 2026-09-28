; A BMC-shaped definitional chain at the base level, queried over several
; rounds: each state is defined from the previous one, and the pushed
; property is checked and retracted per round.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun s0 () (_ BitVec 16))
(declare-fun s1 () (_ BitVec 16))
(declare-fun s2 () (_ BitVec 16))
(declare-fun s3 () (_ BitVec 16))
(assert (= s0 #x0001))
(assert (= s1 (bvshl s0 #x0001)))
(assert (= s2 (bvshl s1 #x0001)))
(push 1)
(assert (= s2 #x0004))
; 1 shifted left twice is 4
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct s2 #x0004))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; deepen the chain between rounds
(assert (= s3 (bvadd s2 s1)))
(push 1)
(assert (= s3 #x0006))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvult s3 #x0006))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
