; RUN: %solver --SMTLIB2 -s --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 -s --uninterpreted-functions --uf-propagate-equalities=off %s 2>&1 | %OutputCheck --check-prefix=OFF %s
;
; The other half of the AUTO decision: a query with no Real content keeps the
; pre-lowering pass. This is the case the pass was written for, and the one
; the Real exemption must not disturb -- on a 40-file QF_UFBV sample, AUTO and
; an explicit `on` solved the same 37 files in the same time, and turning the
; pass off lost four of them and took nearly twice as long.
;
; Paired with uf-prelowering-auto-real.smt2, which is the same shape over
; Real and must reach the opposite decision.
;
; CHECK: UF: pre-lowering
; OFF-NOT: UF: pre-lowering
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x #x03))
(assert (bvugt (f x) (f y)))
(assert (bvult y #x03))
(check-sat)
(exit)
