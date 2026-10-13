; Inside a level the silently kept duplicate was entered twice in the
; level's removal list, and the pop aborted with "Trying to erase function
; which has not been defined". The command is refused before anything is
; stored, so the script ends at the define-fun.
; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
; CHECK: ^\(error "name 'f' already denotes a define-fun"\)$
(define-fun f () Bool (and (! (= x #x01) :named f) (= x #x02)))
(pop 1)
; CHECK-NOT: Trying to erase
; CHECK-NOT: ^sat$
(check-sat)
