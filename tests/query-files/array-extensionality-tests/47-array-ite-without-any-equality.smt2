; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; An array if-then-else with no array equality anywhere in the query.
;
; Replacing every if-then-else where it is built means such a query
; mints two guarded equalities and would otherwise run the whole
; decision procedure for nothing -- measured at 2.4x the CNF and, worse,
; 1023 SAT calls against 1 on a depth-8 if-then-else DAG, because each
; replacement leaves one of its two proxies unconstrained for the solver
; to guess and the checker to refute. restoreArrayITEs puts the
; if-then-elses back when no user equality was ever built, so this ends
; up on the classic path with a byte-identical encoding to --array-
; equality being off. Pins that the answer is right either way.
;
; Unsat by cases on p: d is a if p and b otherwise, and both are made
; to differ from d at i.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 3) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 3) (_ BitVec 8)))
(declare-fun p () Bool)
(declare-fun i () (_ BitVec 3))
(assert (distinct (select (ite p a b) i) (select a i)))
(assert (distinct (select (ite p a b) i) (select b i)))
(check-sat)
