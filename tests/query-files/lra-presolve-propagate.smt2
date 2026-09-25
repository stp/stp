; RUN: %solver --SMTLIB2 --lra-presolve-propagate=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; Under-structure constant propagation: a top-level conjunct is a truth,
; and its occurrences (or its negation's) below other conjuncts fold to
; that truth -- Boolean chains resolve before the solver, a Real atom
; asserted at the top discharges its copy inside a disjunction, and the
; second block shows a chain that flips the verdict the other way.
; CHECK: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
(set-logic QF_LRA)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(assert p)
(assert (or (not p) q))
(assert (or (not q) (<= x 3)))
(push 1)
(assert (>= x 5))
(check-sat)
(pop 1)
(push 1)
(assert (>= x 1))
(check-sat)
(pop 1)
(assert (<= y 5))
(assert (or (not (<= y 5)) r))
(assert (or (not r) (>= y 6)))
(check-sat)
(exit)
