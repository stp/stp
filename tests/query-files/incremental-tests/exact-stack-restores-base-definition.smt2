; Issue #1189: an ordinary solve drops a base definition, then an array
; equality selects an exact-stack block which eliminates one of the
; definition's operands. Restoring that permanent equation must precede
; activation of the block's scoped eliminations.
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

(assert (= (store a i x) b))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: true
; CHECK-NEXT: ^\)$
(get-value ((= (select b i) y)))

(push 1)
(assert (distinct (select b i) y))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)

; Reusing the block must retain both its answer and model interpretation.
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: true
; CHECK-NEXT: ^\)$
(get-value ((= (select b i) y)))
(exit)
