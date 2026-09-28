; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
;
; RUN WITH: --uninterpreted-functions
; EXPECT: unsat, then sat; base declaration survives reset-assertions
(set-logic QF_UFBV)
(set-option :global-declarations true)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun x () (_ BitVec 4))
(assert (distinct (f x) (f x)))
(check-sat)
(reset-assertions)
(assert (= (f x) (f x)))
(check-sat)
