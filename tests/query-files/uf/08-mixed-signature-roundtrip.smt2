; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: REACHED-END
;
; RUN WITH: --uninterpreted-functions
; EXPECT: sat, then REACHED-END
(set-logic QF_UFBV)
(declare-fun b () Bool)
(declare-fun x () (_ BitVec 8))
(declare-fun p (Bool (_ BitVec 8)) Bool)
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 3))
(assert (= (p b x) (p b x)))
(assert (= (f b x) (f b x)))
(check-sat)
(echo "REACHED-END")
