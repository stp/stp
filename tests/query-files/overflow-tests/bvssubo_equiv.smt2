; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvssubo(x,y) iff the 9-bit sign-extended difference isn't a sign-extension of
; its low 8 bits, i.e. its top two bits disagree.
(assert (not (= (bvssubo x y)
  (let ((d (bvsub ((_ sign_extend 1) x) ((_ sign_extend 1) y))))
    (distinct ((_ extract 8 8) d) ((_ extract 7 7) d))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
