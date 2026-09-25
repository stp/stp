; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-relational-last-width=16 -s %s 2>&1 | %OutputCheck --check-prefix=LAST %s
;
; Monotonicity of a product in one factor: x >= 0 and y1 <= y2 give
; x*y1 <= x*y2 in any mode. The exact encoding is two binary32 multipliers
; and a theorem about them, which the SAT solver does not finish in
; minutes; the abstraction's candidate violates the monotonicity fact
; between the two records, the fact is asserted, and the query is unsat
; without either multiplier. With the relational lemmas held until the
; value budget is spent, check that a relational fact is still emitted and
; the query is refuted. A second inconsistent record can queue a release
; in the same round; zero releases is not part of the late-order contract.
; CHECK: ^unsat
; LAST: FpAbstraction: 2 abstracted .* [1-9][0-9]* relational lemmas,
; LAST: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y1 (_ FloatingPoint 8 24))
(declare-const y2 (_ FloatingPoint 8 24))
(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.leq y1 y2))
(assert (not (fp.isNaN (fp.mul RNE x y1))))
(assert (not (fp.isNaN (fp.mul RNE x y2))))
(assert (fp.lt (fp.mul RNE x y2) (fp.mul RNE x y1)))
(check-sat)
