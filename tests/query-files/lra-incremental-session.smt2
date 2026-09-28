; RUN: %solver --SMTLIB2 --lra-incremental-session=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --incremental=off %s | %OutputCheck %s
;
; A pure-QF_LRA push/pop session: the persistent Real session solves each
; check-sat over the kept solver and coordinator, retracting a level on pop.
; Both the session (default) and the batch path (--incremental=off) must
; agree on every verdict.
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 1))
(push 1)
(assert (<= (+ x y) 0))
(check-sat)
(assert (>= y 0))
(check-sat)
(pop 1)
(push 1)
(assert (<= x 0))
(check-sat)
(pop 1)
(push 1)
(assert (>= y 5))
(check-sat)
(pop 1)
(check-sat)
(exit)
