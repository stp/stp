; RUN: %solver --cadical --incremental-auto-engage-at=1 -d %s | %OutputCheck %s
; RUN: %solver --cadical --incremental-auto-engage-at=1 --ackermanize -d %s | %OutputCheck %s
; RUN: %solver --cadical --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --cadical -d %s | %OutputCheck %s
;
; The second check-sat carries an array equality and is small enough for
; the eager instantiation arm, which solves the whole stack as one
; assumption-scoped block under eager Ackermannisation. After the pop the
; stack is the base assertion alone: its model must come from the base
; encoding's read rows, not from the retracted block's. Two things used
; to go wrong here. The eager arm's selection of --ackermanize outlived
; the block (the plain exact-stack return skipped the restore), so the
; next query ran Ackermannised against lazily encoded base rows; and the
; block's read rows stayed in the model-side record, where a row whose
; index evaluates to the same cell as a live base row overwrote the cell
; with an unconstrained value. With v = 0 the base assertion needs
; a[0x0FF] != 0, and the published model said a[0x0FF] = 0.
(set-logic QF_ABV)
(declare-const v (_ BitVec 2))
(declare-const x (Array (_ BitVec 12) (_ BitVec 15)))
(declare-const x1 (Array (_ BitVec 12) (_ BitVec 15)))
(declare-fun a () (Array (_ BitVec 12) (_ BitVec 15)))
(declare-fun a6 () (Array (_ BitVec 16) (_ BitVec 8)))
(assert (distinct (distinct (_ bv0 4) ((_ zero_extend 2) v)) (not (= a (store a ((_ zero_extend 4) (select a6 (_ bv0 16))) (_ bv0 15))))))
(push 1)
; CHECK: ^sat$
(check-sat)
(assert (distinct x x1 (store a ((_ sign_extend 10) ((_ zero_extend 1) ((_ extract 1 1) v))) (_ bv0 15))))
; CHECK: ^sat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
