; RUN: %solver --bb.simplify-during-bb=1 --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; The same abort as simplify-during-bb-fp-constant.smt2, reached with a
; 64-bit float: a Float64 +0.0 constant stored into the array is handed
; to FixedBits::concreteToAbstract by simplify_during_bb, which only
; models bit-vector and boolean constants.
(set-logic QF_ABVFP)
(declare-fun v () (_ BitVec 10))
(declare-fun a () (Array (_ BitVec 5) Float64))
(assert (= (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (select (store a (_ bv0 5) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))) ((_ sign_extend 4) (ite (bvsgt ((_ sign_extend 4) v) (_ bv874 14)) (_ bv1 1) (_ bv0 1))))))
(check-sat)
