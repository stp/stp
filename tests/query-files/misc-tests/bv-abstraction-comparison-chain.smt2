; A refined comparison has to be pinned to the comparison that was asked.
;
; --bv-term-abstraction replaces a comparison with a free Boolean and pins it,
; once the candidate model shows the two disagree, to a chain of clauses over
; the operands' bits. The chain keeps an accumulator when two bits agree and
; overrides it when they differ, so the bit visited *last* among the differing
; ones settles the answer -- which is the most significant one only if the
; chain runs from the least significant bit upwards. It ran downwards, so the
; bottom differing bit won, and what it computed was not `<=` at all: it
; disagreed with `a <= b` on 31616 of the 65536 pairs of eight-bit values.
;
; The lemma then pinned the abstraction to that. Where the pinned value
; contradicted the comparison the query asserts, a satisfiable query came back
; unsat; where it merely disagreed with the model check, the round found the
; abstraction consistent, produced no lemma, and the solve gave up with
;
;   Fatal Error: BV abstraction refinement reached undecided without a
;   pending candidate-blocking lemma
;
; which is this query's symptom. 0xb1 <= (0x31 / c) & b has plenty of models --
; c above two makes the division zero, so it needs c small and b large.
;
; -d re-derives the query under the published model, so the leg is checking
; that the answer is a real one rather than only that a line was printed.
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
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (bvule #xb1 (bvand (bvudiv #x31 c) b)))
(check-sat)
