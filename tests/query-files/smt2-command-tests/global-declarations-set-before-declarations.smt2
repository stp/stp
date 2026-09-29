; Start-only options can be set before set-logic, including after reset.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :global-declarations true)
(set-logic QF_BV)
(set-info :source "STP option-ordering test")
(push 1)
(declare-fun x () (_ BitVec 4))
(pop 1)
(assert (= x #x1))
; CHECK: ^sat$
(check-sat)
(reset)
(set-option :global-declarations true)
(set-logic QF_BV)
(push 1)
(declare-fun y () (_ BitVec 4))
(pop 1)
(assert (= y #x2))
; CHECK-NEXT: ^sat$
(check-sat)
