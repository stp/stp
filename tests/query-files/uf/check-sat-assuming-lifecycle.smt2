; A congruence conflict introduced only by assumptions retracts with those
; assumptions.  This is the useful branch-neutral lifecycle case from the
; peer UF suite; it makes no declaration-scope or error-recovery assumption.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (distinct (f x) (f y)))
(check-sat-assuming ((= x y)))
(check-sat)
(exit)
