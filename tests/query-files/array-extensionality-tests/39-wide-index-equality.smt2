; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Index sort wider than any host integer (66 bits): congruence across
; the equality must compare 66-bit concrete index values by node
; identity, not through a machine word.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 66) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 66) (_ BitVec 8)))
(declare-fun i () (_ BitVec 66))
(assert (= a b))
(assert (distinct (select a i) (select b i)))
(check-sat)
