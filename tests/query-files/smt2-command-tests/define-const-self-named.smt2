; The define-const form of define-fun-self-named.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
; CHECK: ^\(error "name 'c' already denotes a define-fun"\)$
(define-const c Bool (and (! (= x #x01) :named c) (= x #x02)))
; CHECK-NOT: ^sat$
(assert c)
(check-sat)
