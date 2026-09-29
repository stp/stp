; RUN: not %solver %s 2>&1 | %OutputCheck %s
; A comparison of two widths is refused as it is read. bvule over them used
; to be built, and constant-bit propagation then aborted the process on an
; assertion about the operands' widths.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 4))
(assert (bvule x y))
(check-sat)
; CHECK-L: bitvector operands of different widths (8 and 4)
; CHECK-NOT: Assertion
; CHECK-NOT: sat
