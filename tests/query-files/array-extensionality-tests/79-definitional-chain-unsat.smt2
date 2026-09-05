; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Chained definitions: A := B feeds C := store(A, x, y); both substitute
; through, so the read of C at x is y by construction.
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun B () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun C () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 8))
(assert (= A B))
(assert (= C (store A x y)))
(assert (distinct (select C x) y))
(check-sat)
