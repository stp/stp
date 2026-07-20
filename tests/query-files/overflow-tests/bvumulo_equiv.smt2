; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvumulo(x,y) iff the high half of the widened product is nonzero.
(assert (not (= (bvumulo x y)
  (distinct ((_ extract 15 8) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) y))) #x00))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
