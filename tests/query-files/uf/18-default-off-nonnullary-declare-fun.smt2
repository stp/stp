; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: Wrong input logic
; CHECK-NOT: REACHED-END
;
; RUN WITHOUT: --uninterpreted-functions
; EXPECT: exact baseline syntax-error output, parse abandonment, no REACHED-END
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(echo "REACHED-END")
