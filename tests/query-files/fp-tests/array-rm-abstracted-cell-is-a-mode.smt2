; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality -r %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality -r %s | %OutputCheck %s
;
; The same cell, minted on the other route. Sibling of
; array-rm-write-chain-cell-is-a-mode.smt2.
;
; The array transform has two places where it stands a fresh variable in for
; a read of a symbol array: the read-refinement one, and the one taken when
; the complete-array checker is live over the read's array. The first
; disequality here is not a write chain, so it registers a record and the
; checker is live; the five that follow are write chains, which are solved by
; rewriting whatever else is in the query, so their cells are still reads
; minted after FpTotalise ran -- but now they are minted on the checker's
; route. A pin on the refinement route alone leaves them free, and one free
; carrier again satisfies all five at once.
;
; The index is a bit-vector, not a mode. Nothing about the defect or the fix
; depends on the index sort: a chain of one write differs from its base
; exactly when the base's cell at that index differs from the value written,
; whatever sort the index has, and it is the element sort that makes five
; disequalities exhaustive.
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 3) RoundingMode))
(declare-fun b () (Array (_ BitVec 3) RoundingMode))
(declare-fun j () (_ BitVec 3))
(assert (not (= a b)))
(assert (not (= (store b j RNE) b)))
(assert (not (= (store b j RNA) b)))
(assert (not (= (store b j RTP) b)))
(assert (not (= (store b j RTN) b)))
(assert (not (= (store b j RTZ) b)))
(check-sat)
(exit)
