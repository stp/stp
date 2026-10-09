; (get-value v) has no term list. The lexer is waiting for the '(' that opens
; one when it meets the symbol; the symbol must reach the grammar unchanged so
; the grammar's own error is the response, with the script's line.
;
; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; CHECK: ^sat
; CHECK-NEXT: ^\(error "syntax error: line 15 .*expecting LPAREN_TOK.* token: v"\)
; CHECK-NOT: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(check-sat)
(get-value v)
(echo "REACHED-END")
