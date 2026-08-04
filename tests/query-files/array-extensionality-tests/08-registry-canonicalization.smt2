; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Solve-boundary lowering records the write operands before ordinary
; preprocessing substitutes the write index; preparation must recover and
; reason over the operands' current, post-substitution form.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun i () (_ BitVec 2))
(declare-fun j () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun e2 () (_ BitVec 2))
(assert (= j i))
(assert (= (store a j e1) (store b i e2)))
(assert (distinct e1 e2))
(check-sat)
