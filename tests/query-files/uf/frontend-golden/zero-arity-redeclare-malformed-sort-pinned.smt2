; RUN: not %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 11 syntax error, unexpected TERMID_TOK, expecting STRING_TOK  token: s"\)$
; CHECK-NOT: REACHED-END
; CHECK-NOT: BitVec
; A zero-arity redeclaration whose sort is ALSO malformed: the legacy
; grammar died at the name and never saw the sort, so the name-position
; error is the whole response even though bison only fails later, at the
; sort. The parse abandons; the malformed sort adds nothing.
(set-logic QF_UFBV)
(declare-const s (_ BitVec 8))
(declare-fun s () (_ BitVec x))
(check-sat)
(echo "REACHED-END")
