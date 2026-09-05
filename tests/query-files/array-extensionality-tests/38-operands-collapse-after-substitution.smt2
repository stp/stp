; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The disequality is registered over (ite p a b) and a while p is
; still unresolved; the asserted p then folds the if-then-else during
; simplification, so operand recovery finds both canonical operands
; collapsed to the same node. A reflexive disequality can never be
; witnessed: unsat.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(assert p)
(assert (distinct (ite p a b) a))
(check-sat)
