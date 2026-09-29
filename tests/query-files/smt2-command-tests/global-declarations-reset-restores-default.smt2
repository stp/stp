; Reset discards global declarations and restores the option default.
; RUN: not %solver %s | %OutputCheck %s
(set-option :global-declarations true)
(set-logic QF_BV)
(push 1)
(declare-fun kept () (_ BitVec 4))
(pop 1)
(assert (= kept #x1))
; CHECK: ^sat$
(check-sat)
(reset)
; CHECK-NEXT: ^false$
(get-option :global-declarations)
(set-logic QF_BV)
; CHECK-NEXT: .*error.*token: kept.*
(assert (= kept #x1))
