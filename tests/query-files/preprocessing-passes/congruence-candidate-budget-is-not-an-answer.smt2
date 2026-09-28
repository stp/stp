; A candidate is allowed to run out of conflicts: that is what the budget is
; for, and an undecided candidate is simply dropped. What it must not do is
; leave the manager holding the "gave up" flag the candidate raised on its
; way out -- the main query would then report unknown for a query it can
; answer on its own.
;
; One conflict is a budget nothing settles within, so every candidate here
; is abandoned, and the answer still has to be the query's own.
; RUN: %solver --congruence-candidates=1 --congruence-candidate-conflicts=1 %s | %OutputCheck %s
; CHECK: ^unsat$
;
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 24))
(declare-fun b () (_ BitVec 24))
(declare-fun d () (_ BitVec 24))
(assert (= (bvudiv (bvadd (bvmul (_ bv3 24) a) (bvsub b a)) d) (_ bv7 24)))
(assert (= (bvudiv (bvadd (bvadd a a) b) d) (_ bv9 24)))
(check-sat)
(exit)
