; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status sat)
(declare-fun u () (_ BitVec 1))
(assert
 (let ((v (_ bv0 1)))
 (let ((v (_ bv0 1)))
 (= (_ bv0 1) (_ bv0 1)))))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
