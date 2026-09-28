; RUN: %solver --bb.simplify-during-bb=1 --bb.fp-native-arith=1 --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; As simplify-during-bb-fp-native-add-constant-child.smt2, but the operand
; that simplify_during_bb discovers to be constant sits under a
; float-to-float to_fp. With the format lost off the re-made constant the
; conversion's lowering aborted with "FloatBlast expected a floating-point
; source expression".
(set-logic QF_ABVFP)
(declare-fun v () (_ BitVec 1))
(declare-fun y () Float64)
(declare-fun a () (Array (_ BitVec 2) Float32))
(assert (fp.geq (fp.add roundNearestTiesToEven y ((_ to_fp 11 53) roundNearestTiesToEven (select (store a ((_ sign_extend 1) (bvsdiv (_ bv1 1) v)) (fp #b0 #b10000000 #b10000000000000000000000)) (_ bv3 2)))) y))
(check-sat)
