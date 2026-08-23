; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^"REACHED-END"
; Enabling UF support with no reachable application engages no lowering or
; checker work, so the ordinary solver path still supplies the answer.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(check-sat)
(echo "REACHED-END")
