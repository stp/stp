; RUN: not %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: define-fun: the body's sort does not match the declared result sort
; CHECK-NOT: ^sat$
; Reject a definition whose body and declared result have different sorts.
; Immediate-exit behavior must stop before the following check-sat.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 5) (_ BitVec 8)))
(define-fun A0 () (Array RoundingMode (_ BitVec 8)) base)
(check-sat)
