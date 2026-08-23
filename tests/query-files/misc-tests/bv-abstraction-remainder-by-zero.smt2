; The value a remainder abstraction is checked against has to be the one the
; query gives it, division by zero included.
;
; --bv-term-abstraction replaces a wide BVMOD with free bits and decides, from
; the candidate model, whether they are the remainder the operands call for. It
; computed that remainder by long division, and answered zero when the divisor
; is zero. SMT-LIB totalises the two operations differently and does not agree:
; division by zero is all ones, but the remainder is the dividend -- which is
; also what STP's own unabstracted BBDivMod produces, its restoring loop
; finding every shifted remainder at or above a zero divisor, subtracting
; nothing, and handing the dividend back.
;
; So an abstraction holding zero was called consistent on a query whose
; remainder is not zero. Being consistent, it drew no lemma, and the candidate
; the model check had already rejected was the last word:
;
;   Fatal Error: BV abstraction refinement reached undecided without a
;   pending candidate-blocking lemma
;
; The divisor here is (bvxor c b), which the solver is free to make zero, and
; b is the dividend it then has to answer with.
;
; -d re-derives the query under the published model, so the leg checks that
; the answer is a real one and not only that a line was printed.
;
; RUN: %solver --incremental=off -d --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (bvslt (bvand (bvurem b (bvxor c b)) a) a))
(assert (not (bvuge (bvor c a) (bvshl c b))))
(check-sat)
