; Whole-array equality inside the incremental driver: each such round is
; one extensionality block on the persistent solver -- lowered, prepared
; and assumed as a single root, with the consistency checker's lemmas
; encoded into the live solver -- and the stack works across push/pop.
; RUN: %solver --incremental --array-equality %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= (select a #x1) #x11))
(push 1)
; equal arrays cannot disagree on a cell
(assert (= a b))
(assert (= (select b #x1) #x22))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
; ...and agree happily when the cells match
(assert (= a b))
(assert (= (select b #x1) #x11))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
; a disequality needs a witness index, which exists
(assert (distinct a b))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; CHECK-NEXT: ^sat
(check-sat)
; equality asserted at the base level from here on
(assert (= a b))
(push 1)
(assert (= (select b #x1) #x11))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (distinct (select b #x1) #x11))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
