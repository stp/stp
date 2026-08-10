; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^sat
; Generated equality records must not pin declarations or define-fun bodies
; after their scope is popped. The same names are deliberately reused below
; with non-array sorts and a different function body.
(set-logic QF_ABV)

(push 1)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(define-fun f ((i (_ BitVec 1))) Bool (= (store a i #b1) b))
(assert (f #b0))
(check-sat)
(pop 1)

(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(define-fun f ((i (_ BitVec 1))) Bool (= (bvand a i) b))
(assert (f #b0))
(check-sat)
