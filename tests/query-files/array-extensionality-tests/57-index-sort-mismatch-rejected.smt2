; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-L: requires operands of the same sort
; Same index width is not the same index sort: a float-indexed array
; may not be equated with a bitvector-indexed one. Immutable source-sort
; checking rejects this before extensionality lowering.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= a b))
(check-sat)
