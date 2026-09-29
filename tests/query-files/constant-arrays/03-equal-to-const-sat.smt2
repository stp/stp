; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; An array equated with a constant array reads the default everywhere.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)))
(assert (= (select a i) #x07))
(check-sat)
