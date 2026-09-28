; A definitional whole-array equality must likewise leave the protected UF
; leaves registered for direct-CNF refinement rather than substituting them
; out before the solve window opens.
;
; RUN: %solver --uninterpreted-functions --array-equality --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --array-equality --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Fatal Error
; CHECK: ^unsat
;
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (= a b))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
