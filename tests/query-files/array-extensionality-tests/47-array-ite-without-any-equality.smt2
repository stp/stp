; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; An array if-then-else with no array equality anywhere in the query.
;
; This used to leave the registry empty, so the decision procedure was
; never active and STP handled the if-then-else by pushing reads
; through it. Replacing it where it is built means the query now mints
; the replacement's two guarded equalities and runs the full procedure:
; the arrays join the cone, the checker takes over their read
; congruence, and refinement decides it. That is the cost of a
; replacement key nothing can rewrite -- about 2.4x the CNF of the
; classic encoding -- and this pins that the answer is unchanged.
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
