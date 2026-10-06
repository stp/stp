; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |a| () (Array (_ BitVec 1) (_ BitVec 1)) ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b1))
; CHECK-L: (define-fun |b| () (Array (_ BitVec 1) (_ BitVec 1)) ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b1))
; Content, not just shape: over a fully pinned 1-bit domain both cells
; are #b1, so the canonical form is the constant array #b1 rather than
; two stores over a #b0 that no cell holds, and the equal arrays print
; byte-identical bodies -- b's observations arrived purely through
; propagation across the true equality.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= a b))
(assert (= (select a #b0) #b1))
(assert (= (select a #b1) #b1))
(check-sat)
(get-model)
