; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A definitional equality (= A (store B i v)) substitutes A away before
; abstraction; the read of A at i is then v by construction.
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun B () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 8))
(assert (= A (store B x y)))
(assert (distinct (select A x) y))
(check-sat)
