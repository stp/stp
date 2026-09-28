; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Over (Array (_ BitVec 1) (_ BitVec 1)) exactly four arrays exist, so
; five can never be pairwise distinct. Nothing but the witness and
; congruence machinery can see this: every equality is between plain
; symbols, and the pigeonhole emerges from the witness reads of the
; ten abstracted disequalities colliding on the two indices.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun c () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun d () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun e () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (distinct a b c d e))
(check-sat)
