; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun u () (_ BitVec 5))
(assert (not (= (_ bv0 5) (let ((u (_ bv0 5))) u))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
