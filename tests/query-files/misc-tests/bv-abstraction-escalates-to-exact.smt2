; An abstracted multiply stops enumerating and says what it is.
;
; BVMULT, BVDIV and BVMOD are refined by ruling out one pair of operand values
; at a time, which is the only compact lemma there is for them and is why they
; are the three the abstraction can be turned off for on its own. A query the
; solver has to search through can therefore need more rounds than there are
; pairs of operands: this one spent 5816 of them and over ninety seconds,
; against five hundredths of a second unabstracted, and it is a 64-bit
; multiply at the default width floor -- the configuration the flag is meant
; for, not a corner of it.
;
; So a bounded number of blocking lemmas is spent and then the operation is
; encoded exactly, over the same variables the lemmas were already talking
; about: the operand proxies, tied to their real bits or pinned to a constant,
; and the abstraction's own result bits. The abstraction is defined from that
; point, so it is never revisited, and the solve ends with the answer it would
; have given had the term never been abstracted.
;
; Thirty-two is where the measurements put the crossover, and it is the
; ceiling on the allowance rather than the allowance itself: what one blocking
; lemma is worth falls away as the operands widen, so the allowance is
; width/--bv-term-abstraction-value-divisor held under that ceiling. See
; bv-abstraction-value-budget-scales.smt2, which is about the arithmetic; this
; one is about the escalation happening at all and the answer surviving it.
;
; The count is pinned loosely: which candidates the solver offers is its own
; business, so what this fixture holds is that the escalation happens and the
; answer survives it, not the exact round it happens on.
;
; RUN: %solver --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
; RUN: %solver --incremental=off -d --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-mult=0 %s 2>&1 | %OutputCheck --check-prefix=NOMULT %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED: BV abstraction: encoding BVMULT exactly after [0-9]+ blocking lemmas
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
; The opt-out leaves the multiply alone, so nothing escalates and nothing
; enumerates.
; NOMULT-NOT: encoding BVMULT
; NOMULT: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (= (bvmul a b) #x7ffffffc80000005))
(assert (bvugt a #x0000000000000001))
(assert (bvugt b #x0000000000000001))
(check-sat)
