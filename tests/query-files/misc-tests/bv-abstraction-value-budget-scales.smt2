; The allowance a blocking lemma is spent from is a rate, not a number.
; REQUIRES: minisat
;
; --bv-term-abstraction refines an abstracted BVMULT, BVDIV or BVMOD by ruling
; out the one pair of operand values the candidate holds, and gives up after a
; bounded number of those. The bound used to be thirty-two whatever the
; operands were. But a blocking lemma rules out one pair out of 2^(2W), so
; thirty-two of them is a third of an eight-bit operand's pairs and one part
; in 2^101 of a fifty-three-bit one's: the same number is a real budget at one
; end of the range and no budget at all at the other.
;
; So the allowance can be width/--bv-term-abstraction-value-divisor instead,
; floored at one and capped by --bv-term-abstraction-rounds, which stays a
; ceiling and keeps every spelling it had.
;
; The rate is off by default, because it measured as a wash against the flat
; allowance at two abstraction widths with the two differing eightfold in what
; they spend -- see bv_term_abstraction_value_divisor for the numbers. The
; flag is kept for whoever has the wide operands the argument is really about.
; This multiply is 64 bits, so the four legs below ask for the flat default,
; 64/8, 64/4, and a ceiling that bites before any of them.
;
; The count is pinned exactly here, unlike the neighbouring escalation test.
; The allowance arithmetic itself is backend-independent and is covered by
; BVValueLemmaAllowance_Test. This end-to-end trace also needs a solver to keep
; returning inconsistent candidates until that allowance is spent, so it
; selects MiniSat rather than depending on another backend's candidate order.
;
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-value-divisor=8 %s 2>&1 | %OutputCheck --check-prefix=SCALED %s
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=FLAT %s
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-value-divisor=4 %s 2>&1 | %OutputCheck --check-prefix=HALFRATE %s
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-rounds=3 %s 2>&1 | %OutputCheck --check-prefix=CEILING %s
; RUN: %solver --minisat --incremental=off -d -s -t --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-divmod-value-limit=4 %s 2>&1 | %OutputCheck --check-prefix=CAP %s
; RUN: %solver --minisat --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCALED-NOT: Fatal Error
; SCALED: BV abstraction: encoding BVMULT exactly after 8 blocking lemmas
; SCALED: ^sat$
;
; The default leaves the flat ceiling as the allowance, which is what makes
; the two configurations comparable at all: measuring whether the rate helps
; means being able to ask for both in the same binary.
; FLAT: BV abstraction: encoding BVMULT exactly after 32 blocking lemmas
; FLAT: ^sat$
;
; HALFRATE: BV abstraction: encoding BVMULT exactly after 16 blocking lemmas
; HALFRATE: ^sat$
;
; The ceiling still caps, below whatever the rate would have allowed.
; CEILING: BV abstraction: encoding BVMULT exactly after 3 blocking lemmas
; CEILING: ^sat$
;
; The independent cap is DIV/MOD-only: changing it cannot contaminate that
; experiment by changing this multiplication's allowance or outcome. Quick
; statistics still exposes the effective per-record allowance.
; CAP: BV abstraction: encoding BVMULT exactly after 32 blocking lemmas
; CAP: BV abstraction record: record=0 node=[0-9]+ kind=BVMULT width=64 state=exact blocking=32 schemas=[0-9]+ exact=1 exact-bits=64 allowance=32 paired=0 pair-full=0 blocking-clauses=2080 blocking-literals=8224 exact-clauses=[1-9][0-9]* exact-vars=[1-9][0-9]* exact-us=[0-9]+
; CAP: Abstraction refinement: rounds=[0-9]+ blocking=32 schema=[0-9]+ exact=1 exact-mult=1 exact-divmod=0
; CAP: Abstraction circuit cost: clauses=[1-9][0-9]* variables=[1-9][0-9]* microseconds=[0-9]+
; CAP: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) #x7ffffffc80000005))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(check-sat)
