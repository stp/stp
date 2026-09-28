; RUN: %solver --SMTLIB2 -s --lra-theory-propagation=1 %s 2>&1 | %OutputCheck %s
; REQUIRES: default-backend-propagator
;
; Under the theory propagator the tableau is checked on partial assignments,
; at every clause poll, and a conflict found there is handed back as a clause
; before the search has built a whole model on top of it. The three chains
; below are each infeasible only across rows -- no single variable's bounds
; contradict -- so nothing but a simplex check can see it, and the metrics
; must show at least one conflict caught before any complete candidate.
(set-logic QF_LRA)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p q))
(assert (=> p (and (<= (- a b) 0.0) (<= (- b c) 0.0) (<= (- c a) (- 1.0)))))
(assert (=> q (and (<= (- c d) 0.0) (<= (- d a) 0.0) (<= (- a c) (- 1.0)))))
(assert (or (not p) (> d 3.0)))
; CHECK: "partial_conflicts":[1-9]
; CHECK: ^unsat
(check-sat)
