; RUN: %solver --array-equality --ackermanize %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The access-index inventory is shared across every record of one
; array shape, not split per equality: the (a, c) record's witness
; index reaches the (a, b) and (b, c) lemmas, which is what lets the
; chain contradict the distinct witness. No formula read anywhere.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun c () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
