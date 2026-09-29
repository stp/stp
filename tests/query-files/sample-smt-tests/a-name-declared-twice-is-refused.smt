; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; One benchmark declaring a name twice is a syntax error, as it always was.
(benchmark b :logic QF_BV
  :extrafuns ((x BitVec[8]))
  :extrafuns ((x BitVec[8]))
  :formula (= x x))
; CHECK: syntax error: line 6: syntax error  token: x
; CHECK-NOT: ^sat
