; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 --bb.umulo-schulte 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvumulo(x,y) iff the high half of the widened product is nonzero. With the
; idiom recognised both sides are the predicate; with it off the detector
; built from the operands' leading ones and bit 8 of a 9-wide product is
; checked against the 16-wide product; with both off, the old form against
; itself.
(assert (not (= (bvumulo x y)
  (distinct ((_ extract 15 8) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) y))) #x00))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
