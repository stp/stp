; Everything the pass asserts is already implied, so it may not change an
; answer. This is the shape it is most likely to get wrong: an atom that the
; structure leaves free and the arithmetic decides.
; RUN: %solver --skeleton-preproc=1 %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (or (bvult a b) (bvugt a b)))
(assert (= a b))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
