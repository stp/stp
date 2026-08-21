; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
;
; RUN WITH: --uninterpreted-functions
; EXPECT: sat; f and g have independent congruence tables
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(declare-fun g ((_ BitVec 4)) (_ BitVec 8))
(assert (distinct (f x) (g x)))
(check-sat)
