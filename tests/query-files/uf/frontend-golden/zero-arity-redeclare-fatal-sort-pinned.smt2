; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^\(error "syntax error: line 12 syntax error, unexpected TERMID_TOK, expecting STRING_TOK  token: s"\)$
; CHECK-NOT: REACHED-END
; CHECK-NOT: Fatal
; CHECK-NOT: FloatingPoint
; The same pin when the sort rule would have been FATAL (a floating-point
; format too small to exist): the legacy grammar died at the name before
; the sort rule ran, so neither the sort's own message nor a fatal exit may
; appear. The name-position error alone, and the parse abandons.
(set-logic QF_UFBV)
(declare-const s (_ BitVec 8))
(declare-fun s () (_ FloatingPoint 1 1))
(check-sat)
(echo "REACHED-END")
