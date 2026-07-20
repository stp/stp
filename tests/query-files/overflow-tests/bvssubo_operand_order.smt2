; RUN: %solver --difficulty-reversion=0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 1))
; bvssubo(x, 1) is true iff x = 0 (0 - (-1) = 1 overflows the 1-bit signed
; range), so this is satisfiable. The swapped bvssubo(1, x) is false for
; both values of x, so a simplifier that reorders the operands (e.g. via
; SortByArith, which puts constants first) turns this into unsat.
; Difficulty reversion is disabled because it happens to undo the reordering
; on a formula this small, masking the bug.
(assert (bvssubo x (_ bv1 1)))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
