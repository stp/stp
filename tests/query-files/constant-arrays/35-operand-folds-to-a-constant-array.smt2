; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --incremental=on %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Preprocessing turns the third disequality's if-then-else into its constant
; array branch, and the witness read over it folds to the default, leaving
; "name = #b00" where the anchor was. The operand is recovered as that
; constant array; it was reported lost, a fatal error in the batch driver.
(set-logic QF_ABV)
(declare-fun z () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(declare-fun x () (_ BitVec 2))
(assert (not (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) (store (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b01) #b11 #b10) z z))))
(assert (not (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b01) y y))))
(assert (not (= (ite (= z #b00) (store (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) x y) #b00 y) ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00)) (store (store (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) #b10 y) #b01 x) z y))))
(assert (not (= ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) (store (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) #b00 z) z z))))
(check-sat)
