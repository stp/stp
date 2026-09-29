; SMT-LIB 2.7 sections 3.1 and 4.2.9: echo preserves string values and
; quotes, and its specific response replaces success (section 4.1.2).
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^"hello ""world"""$
(echo "hello ""world""")
; CHECK-NEXT: ^""$
(echo "")
; CHECK-NEXT: ^"λ\\path"$
(echo "λ\path")
; CHECK-NEXT: ^success$
(set-option :print-success true)
; CHECK-NEXT: ^"one response"$
(echo "one response")
; CHECK-NEXT: ^"next response"$
(echo "next response")
; CHECK-NOT: success
(set-option :print-success false)
