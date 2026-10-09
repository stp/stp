; A get-value term is scanned twice: the lexer copies its text for the echo,
; then re-reads the copy so the grammar builds the node from the ordinary
; rules. An error inside the term must therefore be reported as it always was,
; against the script's line, and end the script as any other syntax error does.
; Without a term list at all, the grammar's own error is the response.
;
; RUN: not %solver %s 2>&1 | %OutputCheck %s
; RUN: not %solver --incremental=on %s 2>&1 | %OutputCheck %s
;
; CHECK: ^sat
; CHECK-NEXT-L: (
; CHECK-NEXT-L: (v #b111111)
; CHECK-NEXT-L: )
; CHECK-NEXT: ^\(error "syntax error: line 23 .*unexpected STRING_TOK.* token: w"\)
; CHECK-NOT: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(assert (= v #b111111))
(check-sat)
(get-value (v))
(get-value ((bvadd v w)))
(echo "REACHED-END")
