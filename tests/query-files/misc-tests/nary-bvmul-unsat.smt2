; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A product of three odd factors is odd, so it is never 8. The low-bit
; constraints keep the equation out of the word-level solver's reach, so
; the n-ary multiply must actually reach the bit-blaster.
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(declare-const c (_ BitVec 4))
(assert (= (bvmul a b c) (_ bv8 4)))
(assert (= ((_ extract 0 0) a) (_ bv1 1)))
(assert (= ((_ extract 0 0) b) (_ bv1 1)))
(assert (= ((_ extract 0 0) c) (_ bv1 1)))
(check-sat)
