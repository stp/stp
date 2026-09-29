; RUN: %solver -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |a| () (Array (_ BitVec 2) (_ BitVec 2)) (store ((as const (Array (_ BitVec 2) (_ BitVec 2))) #b00) #b00 #b01))
; QF_ABV prints a complete array value even without --array-equality.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(assert (= (select a i) (_ bv1 2)))
(check-sat)
(get-model)
