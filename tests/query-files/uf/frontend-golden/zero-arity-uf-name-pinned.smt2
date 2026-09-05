; RUN: not %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 11 syntax error, unexpected UF_BV_FUNCTIONID_TOK, expecting STRING_TOK  token: g"\)$
; CHECK-NOT: REACHED-END
; The zero-arity pin holds for every classification a known name can
; carry, including the UF-declaration tokens that only exist with the
; feature on: zero-arity declare-fun over a declared uninterpreted
; function replicates the error the classified name would have raised
; before declassification existed, and abandons.
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g () (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
