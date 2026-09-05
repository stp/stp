; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The satisfiable companion of 58: the same pointer-offset write chain
; under an array equality, but with constraints the array axioms do
; allow. A clause strengthened by dropping a folded atom on the wrong
; side would rule this model out and answer unsat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun p () (_ BitVec 32))
(assert (= b (store (store (store a p #x01) (bvadd p #x00000001) #x02)
                    (bvadd p #x00000002) #x03)))
(assert (= (select b (bvadd p #x00000002)) #x03))
(assert (distinct (select b (bvadd p #x00000001)) (select b p)))
(check-sat)
