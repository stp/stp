; The pass proposes one pairing, it is not a theorem, and its sub-solve
; finds a model. That model is the sub-solve's own: the abstraction
; variable of (distinct x4 a) is a free Boolean in it, with no witness behind
; it. The enclosing solve's array-equality checker used to judge it anyway --
; with -d on the eager arm it found the variable false while x4 and a agreed,
; and on the lazy arm it refused a candidate before the array graph was
; bound. Reduced from a fuzzer case.
; RUN: %solver -d --array-equality --congruence-candidates=1 %s | %OutputCheck %s
; RUN: %solver -d --array-equality --congruence-candidates=1 --array-ackermann-budget=0 %s | %OutputCheck %s
; RUN: %solver --array-equality --congruence-candidates=1 --array-ackermann-budget=0 %s | %OutputCheck %s
; CHECK: ^sat
(set-logic QF_ABV)
(declare-const x (_ BitVec 1))
(declare-const x4 (Array (_ BitVec 10) (_ BitVec 4)))
(declare-fun a () (Array (_ BitVec 10) (_ BitVec 4)))
(assert (not (ite (or false (bvsaddo (_ bv0 12) (bvsub (_ bv1 12) ((_ zero_extend 11) x)))) false (distinct false (bvumulo (_ bv0 14) ((_ sign_extend 2) (bvadd (_ bv1 12) ((_ zero_extend 11) (ite (distinct x4 a) (_ bv1 1) (_ bv0 1))))))))))
(check-sat)
(exit)
