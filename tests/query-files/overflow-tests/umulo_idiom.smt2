; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; The double-width spelling of an overflow check, as compiled code writes it,
; with no predicate in sight: the rewrite turns the equality into
; (not (bvumulo x y)). 200 * 2 = 400 does not fit in 8 bits, so the high
; half is nonzero and the query is unsat either way.
(assert (= x #xc8))
(assert (= y #x02))
(assert (= ((_ extract 15 8) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) y))) #x00))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
