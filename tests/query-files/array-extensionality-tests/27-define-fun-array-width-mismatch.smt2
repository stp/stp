; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK-L: define-fun: the body's sort does not match the declared result sort
; CHECK-NOT: ^sat$
; Reject a definition whose body and declared result have different sorts.
; Immediate-exit behavior must stop before the following check-sat.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 3) (_ BitVec 2)) (store base #b00 #b01))
(check-sat)
