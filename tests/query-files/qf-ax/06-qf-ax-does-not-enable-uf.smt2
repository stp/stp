; QF_AX needs uninterpreted carrier sorts, not uninterpreted functions. Its
; set-logic path must not accidentally enable nonzero-arity declare-fun.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK: syntax error, unexpected STRING_TOK, expecting RPAREN_TOK
; CHECK-NOT: REACHED-END
;
(set-logic QF_AX)
(declare-sort U 0)
(declare-fun f (U) U)
(echo "REACHED-END")
