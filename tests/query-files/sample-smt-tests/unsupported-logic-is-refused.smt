; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A benchmark in a logic STP does not decide ends the parse; the grammar
; reported it and then solved the formula anyway.
(benchmark b :logic QF_LIA :extrafuns ((x BitVec[8])) :formula (= x bv1[8]))
; CHECK-L: Wrong input logic:
; CHECK-NOT: ^sat
