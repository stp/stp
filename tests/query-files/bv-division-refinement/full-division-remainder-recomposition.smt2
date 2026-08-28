; A quotient and remainder over identical operands obey the full modular
; recomposition identity x = q*s+r. This is the one fact the abstraction
; states about two operations at once, and the contradiction below lives
; across the complete 256-bit relation.
;
; q=2 and r=1 require a=2b+1, which the final assertion denies.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=divrem-full %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-profile=aggressive %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: paired BVDIV/BVMOD recomposition lemma over 256 bits
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; And it is the one lemma whose cost the escalation counters cannot see. It
; splices a full-width multiplier through the same encoder an escalation uses
; -- it is why this profile is the slowest -- while nothing is given up, so
; the escalation counts stay at zero. A cost line reporting zero here, or no
; cost line at all, would mean the instrumentation added to answer "equal
; escalation counts can hide very different trades" was blind to the largest
; trade the refinement makes.
; RUN: %solver --incremental=off -s -t --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=divrem-full %s 2>&1 | %OutputCheck --check-prefix=COST %s
; COST: Abstraction refinement: rounds=1 blocking=0 schema=1 exact=0 exact-mult=0 exact-divmod=0
; COST-NEXT: Abstraction circuit cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; COST: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= (bvudiv a b) (_ bv2 256)))
(assert (= (bvurem a b) (_ bv1 256)))
(assert (distinct a (bvadd b (bvadd b (_ bv1 256)))))
(check-sat)
(exit)
