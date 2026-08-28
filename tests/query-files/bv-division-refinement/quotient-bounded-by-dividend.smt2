; A quotient cannot exceed its dividend once the divisor is non-zero. Without
; that fact the abstraction has nothing to say about a 256-bit division: it
; spends its blocking lemmas one operand pair at a time and then encodes the
; divider exactly, which does not finish. Timed at 60s before the fact
; existed; milliseconds after.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
;
; The cost of the same lemma, which this bound reaches by the other of the two
; mechanisms a schema can be installed by: written a clause at a time in the
; refiner rather than spliced through the bit-blaster. Both have to be
; reported, because which one a family happens to use is not something a
; reader comparing profiles should have to know. See
; quotient-not-negated-and.smt2 for the spliced half.
;
; RUN: %solver -t --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=base %s 2>&1 | %OutputCheck --check-prefix=COST %s
; COST: Abstraction refinement: rounds=1 blocking=0 schema=1 exact=0
; COST: Abstraction schema cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; COST: base=1
; COST: ^unsat$
;
; There is no exact control leg here, and there cannot be an affordable one:
; the assertion is the negation of the fact, so anything that does not install
; the fact has to prove a 256-bit divider unsatisfiable, which does not finish.
; What this leg establishes is that the fact is offered, named and applied end
; to end at a realistic width -- not that it is true. That is established by
; BVAbstractionLemma_Test, which checks every fact against the operation
; exhaustively below seven bits, by sampling at eight through sixty-four, and
; against the circuit STP blasts for the operation itself.
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (distinct b (_ bv0 256)))
(assert (bvugt (bvudiv a b) a))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
