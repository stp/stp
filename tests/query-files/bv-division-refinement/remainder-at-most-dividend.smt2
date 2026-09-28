; A remainder never exceeds its dividend, over a zero divisor included --
; where the remainder is the dividend. This one STP already decided before
; the fact was added; it is here so that a change which breaks it is caught.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
;
; The EXACT leg answers the same query with no abstraction at all, through
; STP's own divider. Where a fact is installed, reaching unsat is what
; installing a clause that contradicts the assertion does whether or not the
; clause is a theorem, so the two legs disagreeing is the only thing that
; would show a fact that is not one.
; RUN: %solver --incremental=off %s | %OutputCheck --check-prefix=EXACT %s
; EXACT: ^unsat$
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvugt (bvurem a b) a))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
