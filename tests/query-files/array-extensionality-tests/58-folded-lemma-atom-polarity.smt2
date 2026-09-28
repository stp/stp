; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Write indices that are constant offsets from one pointer: the
; simplifying factory decides the index disequalities a refinement
; lemma would otherwise carry, so those atoms are dropped from the
; clause instead of becoming equality circuits.
;
; Dropping is equivalence-preserving on only one side per lemma
; position -- a premise may go when it is valid, the conclusion when it
; is unsatisfiable -- and the two directions are opposite for the same
; "a = b" atom. An encoder that dropped on the wrong side would emit a
; strictly stronger clause, so the answer here would silently become
; unsat for the wrong reason (or, once the direction is checked,
; refuse to encode at all).
;
; Reading b at p steps over the writes at p+2 and p+1, both decided
; distinct from p structurally, and lands on the write of #x01.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun p () (_ BitVec 32))
(assert (= b (store (store (store a p #x01) (bvadd p #x00000001) #x02)
                    (bvadd p #x00000002) #x03)))
(assert (distinct (select b p) #x01))
(check-sat)
