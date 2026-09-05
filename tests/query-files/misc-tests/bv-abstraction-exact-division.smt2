; The exact encoding a division escalates to is the division STP means.
;
; BVDIV and BVMOD escalate the same way BVMULT does, and to the same circuit
; the query would have had if the term had never been abstracted: the
; refinement calls the bit-blaster's own entry point and maps the result to
; CNF through the same ABC pass a plain solve uses, rather than writing
; clauses of its own. It used to write its own -- a second restoring division
; built out of full adders, a comparator and muxes -- and a second
; implementation of a divider is a second thing to get wrong. These two had
; already disagreed once, about a zero divisor.
;
; --bv-term-abstraction-rounds=1 escalates on the second blocking lemma rather
; than the thirty-second, which is how this stays a test of the encoding
; instead of a test of how long the solver takes to get bored. Both the
; quotient and the remainder here are abstracted, so both encoders run.
;
; -d re-derives the query under the published model, so the leg checks the
; answer is a real one and not only that a line was printed. The plain leg is
; the control: escalating is supposed to reach the same answer as never having
; abstracted at all.
;
; RUN: %solver --incremental=off -d -s --bv-term-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction-rounds=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED: BV abstraction: encoding BV(DIV|MOD) exactly after [0-9]+ blocking lemmas
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvudiv a b) c))
(assert (= (bvurem a b) #x0007))
(assert (bvugt c #x0003))
(assert (bvult a #x00ff))
(check-sat)
