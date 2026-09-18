; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
; RUN: %solver --mulo-recognition 0 --bb.smulo-schulte 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvsmulo(x,y) iff the widened product isn't the sign-extension of its low 8
; bits. With the idiom recognised both sides are the predicate; with it off
; the detector built from the bits that differ from the signs and the top
; three bits of a 10-wide product is checked against the 16-wide product;
; with both off, the old form against itself.
(assert (not (= (bvsmulo x y)
  (let ((p (bvmul ((_ sign_extend 8) x) ((_ sign_extend 8) y))))
    (distinct p ((_ sign_extend 8) ((_ extract 7 0) p)))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
