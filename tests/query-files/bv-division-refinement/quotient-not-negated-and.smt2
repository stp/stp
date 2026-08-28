; q != -(s & ~x), for q = x udiv s.
;
; The groups are disjoint: this fact belongs to udiv-observed, so selecting
; the unranked tail on its own must not reach it.
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-observed %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-tail %s 2>&1 | %OutputCheck %s --check-prefix=TAILONLY
; TAILONLY-NOT: quotient-not-negated-and
; CHECK: BV abstraction: BVDIV quotient-not-negated-and lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; ... and what that one lemma cost. This fact is a circuit spliced through
; BVExactEncoder -- the same encoder an escalation goes through -- and for a
; while the cost line covered the full-width installs only, so a run whose
; whole refinement was schema lemmas reported no price at all. A profile is a
; choice of which schema families to enable, so this is the number a profile
; comparison most needs. See quotient-bounded-by-dividend.smt2 for the other
; mechanism, whose clauses are written out in the refiner instead.
;
; Regexes rather than the measured counts: what has to hold is that a price is
; reported and is not zero, and pinning ABC's cut choices would make this a
; test of the mapper.
;
; RUN: %solver -t --incremental=off --bv-term-abstraction=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=udiv-observed %s 2>&1 | %OutputCheck --check-prefix=COST %s
; COST: Abstraction refinement: rounds=1 blocking=0 schema=1 exact=0
; COST: Abstraction schema cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; COST: udiv-observed=1
; COST: ^unsat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 128))
(declare-fun s () (_ BitVec 128))
(assert (= (bvudiv x s) (bvneg (bvand s (bvnot x)))))
(check-sat)
(exit)
