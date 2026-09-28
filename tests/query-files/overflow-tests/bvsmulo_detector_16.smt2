; RUN: %solver --mulo-recognition 0 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(declare-fun y () (_ BitVec 16))
; The signed detector against the 32-wide product tested bit by bit: the
; product fits in 16 bits iff its high 17 bits are all its bit 15.
(assert (not (= (bvsmulo x y)
  (let ((p (bvmul ((_ sign_extend 16) x) ((_ sign_extend 16) y))))
    (not (= ((_ extract 31 15) p) ((_ sign_extend 16) ((_ extract 15 15) p))))))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
