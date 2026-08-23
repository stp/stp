; A refined addition has to be pinned to the sum, not to its complement.
;
; --bv-term-abstraction replaces a wide BVPLUS with free bits and pins them,
; once the candidate model shows they are not the sum, with eight clauses --
; one per assignment of the two operand bits and the carry, each ruling out
; the value the sum bit cannot take. Every one of the eight carried that value
; inverted, so the lemma pinned s = !(l ^ r ^ c): not a weaker constraint on
; the abstraction than the right one, but its negation.
;
; Two things follow, and this query has shown both. The addition stays
; inconsistent on the next round while the abstraction is already marked
; defined, so nothing is ever said about it again and the solve gives up with
;
;   Fatal Error: BV abstraction refinement reached undecided without a
;   pending candidate-blocking lemma
;
; and where the inverted constraint is not merely useless but contradicts what
; the query needs, a satisfiable query comes back unsat -- which is what this
; one did.
;
; The carry clauses were right, so an addition whose operands never carry could
; still come out correct; the operands here are chosen by the solver and do.
;
; -d re-derives the query under the published model, so the leg checks that
; the answer is a real one and not only that a line was printed.
;
; RUN: %solver --incremental=off -d --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (= #x00 (bvand c a)))
(assert (= (bvadd (bvor c a) a) c))
(assert (bvult #x34 (bvshl b c)))
(check-sat)
