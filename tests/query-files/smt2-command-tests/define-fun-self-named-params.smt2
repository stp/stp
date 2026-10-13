; With parameters the dropped body used to surface later, as an arity
; error on the first application. The duplicate definition is the error.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
; CHECK: ^\(error "name 'g' already denotes a define-fun"\)$
(define-fun g ((a (_ BitVec 8))) Bool (and (! (= x #x01) :named g) (= a #x02)))
; CHECK-NOT: differ in number
; CHECK-NOT: ^sat$
(assert (g #x02))
(check-sat)
