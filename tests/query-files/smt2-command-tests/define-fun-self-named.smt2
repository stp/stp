; A :named in a define-fun body may not reuse the function's own name.
; Section 4.1.6 makes the label a define-fun of that name issued just
; before this one, so the command defines the name twice and is an error.
; STP used to keep the label's definition and drop the body silently, so
; f meant (= x #x01) and the assert below answered sat.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
; CHECK: ^\(error "name 'f' already denotes a define-fun"\)$
(define-fun f () Bool (and (! (= x #x01) :named f) (= x #x02)))
; CHECK-NOT: ^sat$
(assert f)
(check-sat)
