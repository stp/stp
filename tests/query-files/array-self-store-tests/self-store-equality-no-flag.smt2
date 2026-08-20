; RUN: %solver %s | %OutputCheck %s
;
; A self-store equality pins one cell: it folds to the read equality at
; the factory, so no whole-array equality is ever built and the query
; runs without --array-equality.
;
; CHECK: ^sat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun j () (_ BitVec 8))
(assert (= a (store a #x03 #x2a)))
(assert (= (select a j) #x2a))
(check-sat)
(exit)
