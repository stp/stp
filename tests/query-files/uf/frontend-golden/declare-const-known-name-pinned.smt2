; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 10 syntax error, unexpected UF_BV_FUNCTIONID_TOK, expecting STRING_TOK  token: f"\)$
; CHECK-NOT: REACHED-END
; declare-const is a UF-free shape: its name is never declassified, so a
; known name -- here a declared uninterpreted function, the only new kind
; of owner the feature introduces -- meets the legacy classified-token
; syntax error at the name and the parse abandons, feature on or off.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const f (_ BitVec 8))
(check-sat)
(echo "REACHED-END")
