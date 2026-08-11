; RUN: %solver --array-equality --ackermanize %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A distinct-arrays witness over an exhausted 2-bit index domain: the
; witness index must alias one of the four constants, where the cells
; are pinned equal. Exercises the witness clause surviving the eager
; path and the Ackermann index-aliasing chains over it.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 4)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 4)))
(assert (= (select a #b00) (select b #b00)))
(assert (= (select a #b01) (select b #b01)))
(assert (= (select a #b10) (select b #b10)))
(assert (= (select a #b11) (select b #b11)))
(assert (not (= a b)))
(check-sat)
