; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 10 syntax error, unexpected BOOL_TOK, expecting RPAREN_TOK  token: Bool"\)
; CHECK-NOT: REACHED-END
;
; RUN WITHOUT: --uninterpreted-functions. The disabled-feature rejection of a
; nonzero-arity declare-fun must stay byte-identical to the baseline grammar,
; which errored at the first domain token and named its kind (not LPAREN's).
(set-logic QF_BV)
(declare-fun f (Bool) (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
