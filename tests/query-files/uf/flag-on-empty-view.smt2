; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^"REACHED-END"
; T-DNH-01 (flag-on arm): declarations with no reachable application
; engage nothing -- no lowering work, no checker, ordinary answers.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(check-sat)
(echo "REACHED-END")
