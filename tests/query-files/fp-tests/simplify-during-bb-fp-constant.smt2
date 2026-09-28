; RUN: %solver --bb.simplify-during-bb=1 --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; A floating-point constant that reaches constant-bit propagation while
; bit-blasting used to abort with Fatal Error: Unexpected:
; BitBlaster::simplify_during_bb hands constant operands to
; FixedBits::concreteToAbstract, which only models bit-vector and boolean
; constants. --bb.simplify-during-bb=1 is what routes the +0.0 / -0.0
; stored below through that path. The guard now skips the FP constant, so
; solving proceeds and the array reads are satisfiable.
(set-logic QF_ABVFP)
(declare-fun v () (_ BitVec 1))
(declare-fun a () (Array (_ BitVec 2) Float32))
(assert (fp.geq (select a (_ bv1 2)) (select (store (store a (_ bv0 2) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))) ((_ sign_extend 1) (bvsdiv (_ bv1 1) v)) (fp (_ bv1 1) (_ bv0 8) (_ bv0 23))) (_ bv0 2))))
(check-sat)
