; The chooser offers the facts a record can receive a bounded number of times
; before the ones whose instance count grows with the width.
;
; The divisor ranges over the 256 powers of two, so the divisor-value family
; applies on every candidate. Its per-exponent facts and the single bound
; `b != 0 -> q <=u a` share the schema-round budget; the bound alone refutes
; this query and must be offered first.
;
; Shift the top bit right to keep a division in the simplified formula.
; The equivalent `1 << k` spelling now becomes a guarded right shift of the
; dividend before abstraction, bypassing the chooser this test exercises.
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
(assert (= b (bvlshr #x8000000000000000000000000000000000000000000000000000000000000000 k)))
(assert (distinct b (_ bv0 256)))
(assert (bvugt (bvudiv a b) a))
(check-sat)
(exit)
