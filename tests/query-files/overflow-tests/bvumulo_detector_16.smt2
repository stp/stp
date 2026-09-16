; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
; The leading-ones detector against the 32-wide product at a width where the
; two circuits share nothing: a*b >= 2^16 whenever bits i of a and j of b are
; set with i + j >= 16, and otherwise iff bit 16 of the 17-wide product.
(assert (not (= (bvumulo x y)
  (not (= ((_ extract 31 16) (bvmul ((_ zero_extend 16) x) ((_ zero_extend 16) y))) #x0000)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
