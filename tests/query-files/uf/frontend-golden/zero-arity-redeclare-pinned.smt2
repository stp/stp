; RUN: not %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 13 syntax error, unexpected TERMID_TOK, expecting STRING_TOK  token: s"\)$
; CHECK-NOT: REACHED-END
; Only malformed nonzero-arity UF declarations adopt report-and-continue.
; A zero-arity declare-fun remains an ordinary scalar declaration and keeps
; the pinned classified-token syntax error and parse abandonment byte-for-byte
; even with the feature on: the lexer declassifies the known name so the
; grammar can see the shape. The zero-arity action then deliberately
; reproduces the same diagnostic that token classification would have raised
; at the name.
(set-logic QF_UFBV)
(declare-fun s () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
