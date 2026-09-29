; The permanent equation restored for #1189 must also constrain later
; ordinary solves after the array-equality block has been popped.
; RUN: %solver --incremental=on --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality --array-ackermann-budget=0 --check-sanity %s | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 3)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 3)))
(declare-fun i () (_ BitVec 2))
(declare-fun x () (_ BitVec 3))
(declare-fun y () (_ BitVec 3))
(declare-fun p () Bool)
(assert (= (ite p x #b100) y))
(assert p)
; CHECK-NEXT: ^sat
(check-sat)

(push 1)
(assert (= (store a i x) b))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: true
; CHECK-NEXT: ^\)$
(get-value ((= (select b i) y)))
(pop 1)

(push 1)
(assert (distinct x y))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

(assert (= x #b010))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: true
; CHECK-NEXT: ^\)$
(get-value ((= y #b010)))

; Enter the exact-stack route again after the ordinary stack grew.
(push 1)
(assert (= (store a i x) b))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: true
; CHECK-NEXT: ^\)$
(get-value ((= (select b i) #b010)))
(pop 1)
(exit)
