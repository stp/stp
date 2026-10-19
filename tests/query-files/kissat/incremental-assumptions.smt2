; REQUIRES: kissat
; RUN: %solver --kissat --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --kissat --incremental=on --kissat-factor=off --kissat-trail-reuse=false -d %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const contradict Bool)
(assert (= (bvmul a b) #x21))
(assert (bvult a b))
(assert (=> contradict (= a b)))
(check-sat)
(check-sat-assuming (contradict))
(check-sat-assuming ((not contradict)))
(push 1)
(assert (= a b))
(check-sat)
(pop 1)
(check-sat)
; Fresh symbols and clauses are introduced after several SAT calls.
(declare-const fresh (_ BitVec 8))
(assert (= fresh (bvadd a b)))
(check-sat)
(assert (distinct fresh (bvadd a b)))
(check-sat)
