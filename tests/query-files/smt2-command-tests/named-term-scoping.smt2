; Labels follow the scoping of define-fun: gone after pop unless
; :global-declarations is true, in which case reset-assertions keeps them
; too. A popped name may be reused by a new label.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :global-declarations true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (! (= x #x01) :named t))
(pop 1)
(assert t)
; CHECK: ^sat$
(check-sat)
; CHECK-L: (t true)
; CHECK-L: (x #x01)
(get-value (t x))
(reset-assertions)
(assert (not t))
; CHECK: ^sat$
(check-sat)
; CHECK-L: (t false)
(get-value (t))
(reset)
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (! (= x #x01) :named t))
(pop 1)
; Without global declarations the name is free again after the pop.
(assert (! (= x #x02) :named t))
; CHECK: ^sat$
(check-sat)
; CHECK-L: (t true)
; CHECK-L: (x #x02)
(get-value (t x))
