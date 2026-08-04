; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; The equality body must remain structural until f is applied. Eager proxy
; creation hides the formal i, making f(0) and f(1) the same Boolean leaf and
; reversing both answers below.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(define-fun f ((i (_ BitVec 1))) Bool
  (= (store a i #b1) b))

; Fix a=[0,0] and b=[1,0], so f(0) is true and f(1) is false.
(assert (= (select a #b0) #b0))
(assert (= (select a #b1) #b0))
(assert (= (select b #b0) #b1))
(assert (= (select b #b1) #b0))

(push 1)
(assert (f #b0))
(assert (not (f #b1)))
(check-sat)
(pop 1)

(push 1)
(assert (f #b0))
(assert (f #b1))
(check-sat)
(pop 1)
