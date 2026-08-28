; The chooser offers the facts a record can receive a bounded number of times
; before the ones whose instance count grows with the width.
;
; Here the divisor is pinned to a power of two, so the divisor-value family
; applies on every candidate: there is one of its facts per exponent, so at
; 256 bits there are 256 of them and they are all violated in turn. They and
; the bound `b != 0 -> q <=u a` are spent from the one schema-round purse,
; and the bound alone refutes this query. Offered second, it was never
; reached: the record spent its thirty-two schema rounds walking exponents,
; then thirty-two blocking lemmas, then built a full 256-bit divider --
; 1,617,712 clauses and 11.75s, against 0.01s for the same query with a
; divisor shaped so the family cannot fire at all.
;
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVDIV quotient-at-most-dividend lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; Run at the default schema groups, because the ordering is what is being
; checked and the default is where it was measured. There is no exact control
; leg and there cannot be an affordable one: without the abstraction this is a
; 256-bit divider to be proved unsatisfiable. That the bound is a theorem is
; established by BVDivSchema_Test and BVAbstractionLemma_Test; what this leg
; establishes is that it is the fact a round buys.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun k () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= b (bvshl (_ bv1 256) k)))
(assert (distinct b (_ bv0 256)))
(assert (bvugt (bvudiv a b) a))
(check-sat)
(exit)
