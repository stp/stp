; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: syntax error, unexpected LPAREN_TOK, expecting RPAREN_TOK
; CHECK-NOT: REACHED-END
;
; QF_AUFBV is an accepted host logic even with UFSTP disabled. Its spelling
; must not, however, enable non-nullary uninterpreted functions.
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(echo "REACHED-END")
