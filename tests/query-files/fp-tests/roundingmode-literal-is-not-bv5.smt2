; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; RNE and #b00001 have equal target bits but different source sorts.
; CHECK: = requires operands of the same sort
(assert (= RNE #b00001))
(check-sat)
