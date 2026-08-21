; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
;
; With global declarations enabled, popping retracts only the assertion. The
; declaration and its durable application remain usable in the outer frame.
(set-option :global-declarations true)
(set-logic QF_UFBV)
(push 1)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (distinct (f x) (f x)))
(check-sat)
(pop 1)
(assert (= (f x) (f x)))
(check-sat)
