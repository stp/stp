; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: f expects 1 argument but was applied to 2
; CHECK: ^sat
; CHECK: REACHED-END
;
; RUN WITH: --uninterpreted-functions
; EXPECT: one nonfatal arity error, then sat, then REACHED-END
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 4))
(assert (= (f x x) #b0000))
(check-sat)
(echo "REACHED-END")
