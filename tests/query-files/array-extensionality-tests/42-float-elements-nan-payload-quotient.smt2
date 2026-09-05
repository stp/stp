; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Every NaN bit pattern denotes the one NaN value, so arrays that are
; pointwise = at every index of the domain are equal: a witness for
; their disequality may not be two cells that differ only in NaN
; payload. (Answered sat before the witness clause quotiented NaN.)
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(assert (not (= a b)))
(assert (= (select a #b0) (select b #b0)))
(assert (= (select a #b1) (select b #b1)))
(check-sat)
