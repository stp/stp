; RUN: not %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 11 syntax error, unexpected NUMERAL_TOK, expecting RPAREN_TOK  token: 8"\)
; CHECK-NOT: REACHED-END
;
; RUN WITHOUT: --uninterpreted-functions. A first domain token outside the
; UF sort grammar's FIRST set reaches the declaration branch through Bison's
; default reduction; the rejection must name that lookahead just as the
; baseline grammar did.
(set-logic QF_BV)
(declare-fun f (8) (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
