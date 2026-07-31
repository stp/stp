; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat
; An array if-then-else with no array equality anywhere in the query.
;
; Nothing here asks for whole-array reasoning, so nothing should pay
; for it: the elimination of section 4.1 runs only for a query that
; abstracted an equality, and this one is decided by STP's ordinary
; array machinery at exactly the cost it would pay with the option off.
; What it would cost otherwise is not the extra clauses -- each
; replacement leaves one of its two proxies unconstrained under any
; assignment of the condition, so the solver guesses and the checker
; refutes, one lemma at a time. Measured on a depth-8 if-then-else DAG:
; 1023 SAT calls against 1, and 20x the wall clock. Pins that the
; answer is right either way.
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
