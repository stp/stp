; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)

; An ill-sorted = between different bitvector widths must be diagnosed, not
; silently folded to false and "solved" as unsat. Regression test: the
; floating-point extension of the EQ type check used to accept any width
; pair, and the simplifying factory folds constant operands before any type
; check can see them.
; CHECK: = requires operands of the same sort
(assert (= #x00000001 #x0000000000000001))
(check-sat)
