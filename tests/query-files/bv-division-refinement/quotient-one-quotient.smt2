; If exactly one subtraction of b fits in a, the quotient is one:
;
;   b <=u a and (a-b) <u b -> a udiv b = 1.
;
; The first run also keeps multiplication abstraction off. Division must
; still be abstracted and refined, which is the end-to-end check that the
; new DIV/MOD scope switch is independent rather than merely exposed in the
; option structures.
;
; RUN: %solver --incremental=off -s --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schema-groups=quotient-one-quot %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=off -s -t --bv-term-abstraction=1 --bv-term-abstraction-mult=0 --bv-term-abstraction-divmod=1 --bv-term-abstraction-plus=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-schemas=0 --bv-term-abstraction-divmod-value-limit=1 %s 2>&1 | %OutputCheck --check-prefix=CAP %s
; CHECK: BV abstraction: BVDIV quotient-is-one lemma
; CHECK-NEXT: BV abstraction: refined 1 operations
; CHECK: ^unsat$
;
; CAP: BV abstraction: encoding BVDIV exactly after 1 blocking lemmas
; CAP: BV abstraction record: record=0 node=[0-9]+ kind=BVDIV width=256 state=exact blocking=1 schemas=0 exact=1 exact-bits=256 allowance=1 paired=0 pair-full=0 blocking-clauses=256 blocking-literals=131328 exact-clauses=[1-9][0-9]* exact-vars=[1-9][0-9]* exact-us=[0-9]+
; CAP: Abstraction refinement: rounds=2 blocking=1 schema=0 exact=1 exact-mult=0 exact-divmod=1
; CAP: Abstraction circuit cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; CAP: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (bvule b a))
(assert (bvult (bvsub a b) b))
(assert (distinct (bvudiv a b) (_ bv1 256)))
(check-sat)
(exit)
