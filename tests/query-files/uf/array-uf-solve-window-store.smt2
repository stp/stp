; The batch solve window must protect UF result scalars while array equality
; propagation and unconstrained elimination process an accepted store
; equality.  Otherwise the congruence semantics can be substituted away.
;
; RUN: %solver --uninterpreted-functions --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(declare-const e1 (_ BitVec 8))
(declare-const e2 (_ BitVec 8))
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= (store a i e1) (store b j e2)))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
