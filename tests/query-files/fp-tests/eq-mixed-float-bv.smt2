; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_FP)

; = between a float and a bitvector is ill-sorted in either operand order.
; Regression test: with the float FIRST this used to be accepted silently as
; raw bit equality, because the scan deciding =-over-floats skipped operand 0.
; CHECK: requires operands of the same sort
(assert (= ((_ to_fp 8 24) #x00000000) #x00000000))
(check-sat)
