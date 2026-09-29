; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|f\|
;
; EXPECT: sat
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun f ((_ BitVec 4)) (_ BitVec 8))
(assert (distinct x y))
(assert (= (f x) (f y)))
(check-sat)
(get-model)
