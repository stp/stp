; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: syntax error
; CHECK: ^unsat
;
; QF_AUFBV contains UF and therefore enables non-nullary functions itself.
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (distinct (f #x00) (f #x00)))
(check-sat)
