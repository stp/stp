; reset empties the assertion stack and takes every declaration with it,
; global ones included -- but not the option itself, which says how the
; declarations made after it are to be scoped. A driver that resets between
; problems therefore does not have to set :global-declarations again.
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
; CHECK-NEXT: ^true$
(get-option :global-declarations)
(set-logic QF_BV)
(push 1)
(declare-fun after_reset () (_ BitVec 4))
(pop 1)
(assert (= after_reset #x2))
; CHECK-NEXT: ^sat$
(check-sat)
; The declarations made before the reset did not survive it, so this name is
; unknown again.
; CHECK-NEXT: .*error.*token: kept.*
(assert (= kept #x1))
(check-sat)
