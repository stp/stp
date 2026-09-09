; The relation's fresh quotient and remainder are constrained only by the
; relation conjoined into the root they were minted under. The incremental
; driver blasts every block through one blaster, so a remainder asked for in
; a later block must not pick up the pair a popped block minted for the same
; operands: before the memo was cleared per root, the second block below
; came back sat with a free remainder, as did the old --bb.div-by-mult
; relation. The third block reuses the division term itself across blocks.
;
; RUN: %solver --bb.div-by-const-width=8 --incremental=on %s | %OutputCheck %s
; RUN: %solver --bb.div-by-const-width=8 --incremental=off %s | %OutputCheck %s
; RUN: %solver --bb.div-by-const=0 --bb.div-by-mult=1 --incremental=on %s | %OutputCheck %s
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
; CHECK: ^unsat$
;
; EXPECT: unsat, four times
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (bvugt (bvudiv x #x0b) x))
(check-sat)
(pop 1)
(push 1)
(assert (bvuge (bvurem x #x0b) #x0b))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvudiv x #x0b) #x01))
(assert (bvugt x #x30))
(check-sat)
(pop 1)
(push 1)
(assert (= (bvurem x #x0b) #x01))
(assert (bvult x #x0b))
(assert (bvugt x #x01))
(check-sat)
(pop 1)
