; The allowance a blocking lemma is spent from is a rate, not a number.
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
; The count is pinned exactly here, unlike the neighbouring escalation test:
; which candidates the solver offers is its own business, but *how many* it is
; allowed to be offered before the refinement gives up is not -- that is the
; arithmetic this test is about, and it is the same whatever the solver does.
;
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-value-divisor=8 %s 2>&1 | %OutputCheck --check-prefix=SCALED %s
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=FLAT %s
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-value-divisor=4 %s 2>&1 | %OutputCheck --check-prefix=HALFRATE %s
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-rounds=3 %s 2>&1 | %OutputCheck --check-prefix=CEILING %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
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
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) #x7ffffffc80000005))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(check-sat)
