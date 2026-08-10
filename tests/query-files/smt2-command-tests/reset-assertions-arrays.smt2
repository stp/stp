; RUN: %solver %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun i () (_ BitVec 4))
(assert (and (= (select a i) #x1) (= (select a i) #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
(reset-assertions)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))
(declare-fun i () (_ BitVec 4))
(assert (= (select a i) #x1))
; CHECK-NEXT: ^sat
(check-sat)
