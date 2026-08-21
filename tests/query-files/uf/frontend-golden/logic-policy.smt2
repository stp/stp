; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(check-sat)
(reset)
(set-logic QF_AUFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (g (select a #x00)) (g (select a #x00))))
(check-sat)
