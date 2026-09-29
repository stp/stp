; RUN: %solver %s | %OutputCheck %s
(set-option :print-success true)
; CHECK-NEXT: ^success$
(set-info :source "a string with ""quotes"", ; and )")
; CHECK-NEXT: ^success$
(set-info :extensions
  (! _ as let forall exists match par
     (declare-const x Bool) :keyword #b0101 #xAf 2.7
     "string with )" |symbol with )| ; comment with (
     (() (:nested true))))
; CHECK-NEXT: ^success$
(set-info :flag)
; CHECK-NEXT: ^success$
; Unsupported extensions still accept the general attribute syntax.
(set-option :extension (one (two :three) "four"))
; CHECK-NEXT: ^unsupported$
(set-option :extension)
; CHECK-NEXT: ^unsupported$
(set-logic QF_BV)
; CHECK-NEXT: ^success$
(declare-const source Bool)
; CHECK-NEXT: ^success$
(set-info :source source)
; CHECK-NEXT: ^success$
(assert source)
; CHECK-NEXT: ^success$
(check-sat)
; CHECK-NEXT: ^sat$
