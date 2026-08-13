; Because a popped declaration is gone, its name is free again -- and may come
; back at a different sort. This is the observable difference between the two
; settings of the option: the identical script must be rejected when
; :global-declarations is true (see global-declarations-true-redeclare-is-error).
; RUN: %solver %s | %OutputCheck %s
(set-option :global-declarations false)
; get-model is only answered when a model was asked for; an assertions
; build constructs one either way, so without this the test passes there and
; fails in a release build.
(set-option :produce-models true)
(set-logic QF_BV)
(push 1)
(declare-fun x!0 () Bool)
(assert (not x!0))
; CHECK: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\(define-fun \|x!0\| \(\) Bool false\)$
; CHECK-NEXT: ^\)$
(get-model)
(pop 1)
(push 1)
(declare-fun x!0 () (_ BitVec 32))
(assert (= x!0 (_ bv0 32)))
; CHECK-NEXT: ^sat$
(check-sat)
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\(define-fun \|x!0\| \(\) \(_ BitVec 32\) #x00000000\)$
; CHECK-NEXT: ^\)$
(get-model)
