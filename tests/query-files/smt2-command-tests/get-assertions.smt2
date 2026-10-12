; get-assertions is unsupported: STP stores what its node factory made of
; each assertion, and the standard requires the formula as it was asserted.
; The option that would enable the command is unsupported too, and the
; script continues past both.
; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsupported$
(set-option :produce-assertions true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^unsupported$
(get-option :produce-assertions)
; CHECK-NEXT: ^unsupported$
(get-assertions)
; CHECK-NEXT: ^sat
(check-sat)
