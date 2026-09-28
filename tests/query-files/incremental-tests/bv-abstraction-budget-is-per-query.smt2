; The blocking allowance is a per-query budget on both drivers.
;
; --bv-term-abstraction-rounds is a ceiling on what one abstraction may spend
; before the refinement gives up and encodes it exactly, and the numbers behind
; the defaults were measured a query at a time. A record's life is one query in
; the batch pipeline, but a whole session under the incremental driver, where
; records are dropped only by a rebuild -- so spent from a lifetime count the
; same flag meant two different things, and this session gave up on the
; multiplication after two blocking lemmas spread over two queries rather than
; two within one.
;
; The multiplication here is asserted at the base level, so it is live for
; every check-sat. Each of the five that follow pins both operands to fresh
; values, which costs the record exactly one blocking lemma -- below the
; ceiling of two, so it never escalates. Read from the lifetime count it
; passes the ceiling on the third and installs a 33,968-clause multiplier
; there; that is what this leg is for.
;
; The record dumps still report the lifetime spend, which is what the
; diagnostics are for and is unchanged: it climbs 1, 2, 3, 4, 5 while state
; stays open and exact stays zero.
;
; RUN: %solver --incremental=on -t --bv-term-abstraction=1 --bv-term-abstraction-schemas=0 --bv-term-abstraction-compare=0 --bv-term-abstraction-rounds=2 %s 2>&1 | %OutputCheck --check-prefix=BUDGET %s
; RUN: %solver --incremental=on -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; BUDGET: kind=BVMULT width=64 state=open blocking=1 schemas=0 exact=0
; BUDGET: kind=BVMULT width=64 state=open blocking=2 schemas=0 exact=0
; BUDGET: kind=BVMULT width=64 state=open blocking=3 schemas=0 exact=0
; BUDGET: kind=BVMULT width=64 state=open blocking=4 schemas=0 exact=0
; BUDGET: kind=BVMULT width=64 state=open blocking=5 schemas=0 exact=0
; BUDGET-NOT: BV abstraction: encoding BVMULT exactly
;
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))
(assert (bvult (bvmul x y) (_ bv18446744073709551615 64)))
(push 1)
(assert (= x (_ bv1000003 64)))
(assert (= y (_ bv65537 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1007922 64)))
(assert (= y (_ bv170266 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1015841 64)))
(assert (= y (_ bv274995 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1023760 64)))
(assert (= y (_ bv379724 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1031679 64)))
(assert (= y (_ bv484453 64)))
(check-sat)
(pop 1)
(exit)
