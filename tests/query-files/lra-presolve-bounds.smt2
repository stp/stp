; RUN: %solver --SMTLIB2 --lra-presolve-bounds=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Bound-driven simplification under the Boolean structure: top-level unit
; bounds decide atoms buried in disjunctions -- x <= 5 refutes x > 7 in
; the first block's disjunct, and 3 <= x <= 4 implies x <= 10 in the
; second, driving each Boolean chain to its verdict before the solver.
; CHECK: ^unsat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun r () Bool)
(declare-fun q () Bool)
(push 1)
(assert (<= x 5))
(assert (or (> x 7) r))
(assert (or (not r) q))
(assert (not q))
(check-sat)
(pop 1)
(push 1)
(assert (>= x 3))
(assert (<= x 4))
(assert (or (not (<= x 10)) r))
(assert (or (not r) (>= y 1)))
(assert (< y 1))
(check-sat)
(pop 1)
(assert (>= x 3))
(assert (<= x 4))
(assert (or (not (<= x 10)) (>= y 1)))
(check-sat)
(exit)
