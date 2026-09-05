; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |a| (_ BitVec 2) (_ BitVec 2) #b00 #b01)
; The counterexample holds a solver-map read at the symbolic index i
; next to the concrete observation; printing the model must order the
; two without demanding constant bits of i.
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(assert (= (select a i) (_ bv1 2)))
(check-sat)
(get-model)
