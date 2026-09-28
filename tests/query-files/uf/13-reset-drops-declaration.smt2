; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
;
; RUN WITH: --uninterpreted-functions
; EXPECT: sat, sat; reset destroys declarations and permits a changed signature
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun x () (_ BitVec 4))
(assert (= (f x) (f x)))
(check-sat)
(reset)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) Bool)
(declare-fun y () (_ BitVec 8))
(assert (= (f y) (f y)))
(check-sat)
