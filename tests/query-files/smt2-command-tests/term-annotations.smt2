; RUN: %solver %s | %OutputCheck %s
(set-option :produce-models true)
(set-option :produce-assertions true)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (= x (! #x2a :custom (as let _ ! :nested "data") :named value))
           :named equality :another-flag))
(assert (! (= (! x :named first :extra 0) first) :irrelevant true))
; CHECK: ^sat$
(check-sat)
; The annotation is an inline definition; it adds no asserted equality.
; CHECK: ^\($
; CHECK: = \|x\| +#x2A
; CHECK-NOT: \|equality\|
; CHECK-NOT: \|value\|
(get-assertions)
; Definitions are absent from get-model, which describes declared symbols.
; CHECK: define-fun \|x\|
; CHECK-NOT: define-fun \|equality\|
; CHECK-NOT: define-fun \|value\|
(get-model)
(get-value (value first equality))
(push 1)
(assert (! true :named temporary))
(pop 1)
(define-const temporary Bool true)
; Closed terms may contain their own local binders.
(assert (! (let ((p true)) p) :named with-let))
; An unrelated enclosing binder does not make a term open.
(assert (let ((p true)) (! true :named unused-binder)))
(assert (and with-let unused-binder temporary))
; CHECK: ^sat$
(check-sat)
