; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |a| () (Array (_ BitVec 1) (_ BitVec 1)) (store ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b0) #b0 #b1))
; With the option on but no array equality anywhere in the query, the
; model printer still uses the store-chain define-fun form, fed by a
; counterexample populated purely by classic refinement. (This is a
; deliberate difference from the option-off run of the same file,
; which keeps the pre-feature array printer.)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= (select a #b0) #b1))
(check-sat)
(get-model)
