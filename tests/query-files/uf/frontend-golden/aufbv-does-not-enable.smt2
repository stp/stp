; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: syntax error, unexpected LPAREN_TOK, expecting RPAREN_TOK
; CHECK-NOT: REACHED-END
;
; QF_AUFBV is an accepted host logic while uninterpreted-function support is
; disabled. Its spelling must not enable non-nullary functions by itself.
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(echo "REACHED-END")
