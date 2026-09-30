; The seed is session-wide and reset restores its startup default.
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^0$
(get-option :random-seed)
; CHECK-NEXT: ^success$
(set-option :print-success true)
; CHECK-NEXT: ^success$
(set-option :random-seed 42)
; CHECK-NEXT: ^42$
(get-option :random-seed)
; CHECK-NEXT: ^success$
(set-logic QF_BV)
; CHECK-NEXT: ^success$
(set-option :random-seed 18446744073709551615)
; CHECK-NEXT: ^18446744073709551615$
(get-option :random-seed)
; CHECK-NEXT: ^success$
(push 1)
; CHECK-NEXT: ^success$
(set-option :random-seed 1)
; CHECK-NEXT: ^success$
(pop 1)
; CHECK-NEXT: ^1$
(get-option :random-seed)
; CHECK-NEXT: ^success$
(reset-assertions)
; CHECK-NEXT: ^1$
(get-option :random-seed)
(reset)
; CHECK-NEXT: ^0$
(get-option :random-seed)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
; The seed can also be set after assertions.
(set-option :random-seed 4294967296)
; CHECK-NEXT: ^4294967296$
(get-option :random-seed)
; CHECK-NEXT: ^sat$
(check-sat)
(reset-assertions)
; CHECK-NEXT: ^4294967296$
(get-option :random-seed)
(set-option :random-seed 0)
; CHECK-NEXT: ^0$
(get-option :random-seed)
; CHECK-NEXT: ^sat$
(check-sat)
