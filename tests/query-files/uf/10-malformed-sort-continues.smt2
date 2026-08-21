; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: argument 0 of f has sort Bool but the declaration requires \(_ BitVec 8\)
; CHECK: ^sat
; CHECK: REACHED-END
;
; RUN WITH: --uninterpreted-functions
; EXPECT: one nonfatal sort error, then sat, then REACHED-END
(set-logic QF_UFBV)
(declare-fun b () Bool)
(declare-fun f ((_ BitVec 8)) Bool)
(assert (f b))
(check-sat)
(echo "REACHED-END")
