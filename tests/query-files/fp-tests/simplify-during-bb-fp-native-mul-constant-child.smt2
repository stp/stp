; RUN: %solver --bb.simplify-during-bb=1 --bb.fp-native-arith=1 --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; As simplify-during-bb-fp-native-add-constant-child.smt2, over fp.mul with
; a -1.0 operand: the constant the blaster discovers also drives the
; simplifying factory's fold of x * -1.0, which builds new floating-point
; structure over the re-made constant. Before getConstant kept the format
; this aborted with "argument to <fp> is not an fp".
(set-logic QF_ABVFP)
(declare-fun v () (_ BitVec 1))
(declare-fun x () Float32)
(declare-fun a () (Array (_ BitVec 2) Float32))
(assert (fp.gt (fp.mul roundTowardZero x (select (store a ((_ sign_extend 1) (bvsdiv (_ bv1 1) v)) (fp #b1 #b01111111 #b00000000000000000000000)) (_ bv3 2))) x))
(check-sat)
