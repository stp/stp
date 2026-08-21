; QF_AUFBVFP is gated on the feature exactly as its aliases and QF_UFBV are:
; with --uninterpreted-functions absent it is not a logic STP admits, and the
; report is the ordinary recoverable wrong-logic error rather than anything
; UF-specific.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: Wrong input logic
; CHECK-NEXT: ^sat
;
(set-logic QF_AUFBVFP)
(check-sat)
