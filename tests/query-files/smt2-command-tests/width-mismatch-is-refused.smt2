; RUN: not %solver %s 2>&1 | %OutputCheck %s
; Operands of two widths are refused as the term is read. bvsub over them
; used to be built anyway and the query answered, under no defined
; semantics.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 4))
(assert (= (bvsub x y) x))
(check-sat)
; CHECK-L: bitvector operands of different widths (8 and 4)
; CHECK-NOT: sat
