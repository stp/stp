; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 4))
; Operands of different widths extended to 16 with the high 8 bits tested:
; the product is exact (16 >= 8 + 4) and the test width 8 covers both
; operands, so this is (not (bvumulo x (zero_extend 4 y))). 128 * 2 = 256
; overflows 8 bits; 127 * 2 does not.
(assert (= y #x2))
(assert (= ((_ extract 15 8) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 12) y))) #x00))
(assert (bvuge x #x7f))
; CHECK-NEXT: ^sat
(check-sat)
(assert (bvuge x #x80))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
