; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
;
; RUN WITH: --uninterpreted-functions
; EXPECT: sat, sat; the popped declaration is removed and may be redeclared
(set-logic QF_UFBV)
(push 1)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-fun x () (_ BitVec 4))
(assert (= (f x) (f x)))
(check-sat)
(pop 1)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (f y) (f y)))
(check-sat)
