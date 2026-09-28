; RUN: not %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: syntax error, unexpected LPAREN_TOK, expecting RPAREN_TOK
; CHECK-NOT: REACHED-END
;
; RUN WITHOUT: --uninterpreted-functions
; EXPECT: exact baseline syntax-error output, parse abandonment, no REACHED-END
; reset clears a logic-selected UF mode. A following logic that does not
; contain UF therefore leaves the frontend disabled.
(set-logic QF_UFBV)
(reset)
(set-logic QF_BV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(echo "REACHED-END")
