; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 13 syntax error, unexpected TERMID_TOK, expecting STRING_TOK  token: s"\)$
; CHECK-NOT: REACHED-END
; FE-05 / FE-07 keep their scope: only the NONZERO-ARITY (UF) declaration
; shape adopts report-and-continue. A ZERO-ARITY redeclaration -- the
; UF-free shape -- keeps the pinned classified-token syntax error and
; parse abandonment byte-for-byte even with the feature ON: the lexer
; declassifies the known name so the grammar can see the shape, and the
; zero-arity action replicates exactly the error the classification
; would have raised at the name.
(set-logic QF_UFBV)
(declare-fun s () (_ BitVec 8))
(declare-fun s () (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
