; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: unsupported
; CHECK: error
; Without --array-equality, a nullary array-sorted define-fun keeps the
; pre-feature unsupported behavior.
(set-logic QF_ABV)
(declare-fun base () (Array (_ BitVec 2) (_ BitVec 2)))
(define-fun A0 () (Array (_ BitVec 2) (_ BitVec 2)) (store base (_ bv0 2) (_ bv1 2)))
(assert (= (select A0 (_ bv0 2)) (_ bv1 2)))
(check-sat)
