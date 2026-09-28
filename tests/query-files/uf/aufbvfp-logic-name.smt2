; The canonical array+UF+BV+FP spelling selects both FP tokens and the UF
; frontend without an extra command-line option.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: Wrong input logic
; CHECK: ^unsat
;
(set-logic QF_AUFBVFP)
(declare-fun f (RoundingMode) RoundingMode)
(assert (distinct (f RNE) (f RNE)))
(check-sat)
