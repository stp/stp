; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat

(set-logic QF_BV)
(declare-const bv_40-0 (_ BitVec 40))
(assert (bvugt (bvurem ((_ rotate_right 6) bv_40-0) bv_40-0) bv_40-0))
(check-sat)