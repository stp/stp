; RUN: %solver --bb.simplify-during-bb=1 --bb.fp-native-arith=1 --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; The select's index is constant only at the bit level (1 sdiv v is 1 for
; both values of v), so the word-level simplifier leaves the select alone
; and simplify_during_bb is what discovers, mid-blast, that the fp.add's
; float operand is a constant. getConstant used to re-make that operand as
; a plain BVCONST -- the FLOATINGPOINT format does not survive -- and the
; rebuilt fp.add failed BVTypeCheck with "argument to <fp> is not an fp".
; --bb.fp-native-arith=1 is what keeps the fp.add alive into the
; bit-blaster; getConstant now re-makes the operand as an ASTFPConst.
(set-logic QF_ABVFP)
(declare-fun v () (_ BitVec 1))
(declare-fun x () Float32)
(declare-fun a () (Array (_ BitVec 2) Float32))
(assert (fp.geq (fp.add roundNearestTiesToEven x (select (store a ((_ sign_extend 1) (bvsdiv (_ bv1 1) v)) (fp #b0 #b10000000 #b10000000000000000000000)) (_ bv3 2))) x))
(check-sat)
