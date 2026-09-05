; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-L: requires operands of the same sort
; Same packed width is not the same sort: a float-element array may
; not be equated with a bitvector-element array. Immutable source-sort
; checking rejects this before extensionality lowering.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 32)))
(assert (= a b))
(check-sat)
