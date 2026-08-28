; x <u s -> x urem s = x. This is the cheapest fact in the imported
; remainder family and settles the operation outright.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=urem %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: BVMOD dividend-below-divisor lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; The leg above installs the fact and reaches unsat, which is what installing
; a clause that contradicts the assertion does whether or not the clause is a
; theorem. The EXACT leg answers the same query with no abstraction at all,
; through STP's own divider, so a fact that were not a theorem would show as a
; disagreement between the two rather than as a green run.
; RUN: %solver --incremental=off %s | %OutputCheck --check-prefix=EXACT %s
; EXACT: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 256))
(declare-fun s () (_ BitVec 256))
(assert (bvult x s))
(assert (distinct (bvurem x s) x))
(check-sat)
(exit)
