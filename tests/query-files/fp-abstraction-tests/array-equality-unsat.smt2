; An array equality over an abstracted product. The array holds the
; product of x1 and y, and the read of it is compared against the product
; of y and x2 with x1 and x2 equal, so the two products are one value and
; the query is unsat. The exact encoding has to prove that a binary32
; multiplier commutes, which the SAT solver does not finish in minutes;
; the abstraction's candidate gives the two records different values, the
; congruence fact between them is asserted, and the query is refuted
; without either multiplier.
;
; The candidate that gives them different values is refuted by the exact
; product, and the array checker has certified its contents relative to
; the surrogate, so the model repair must not accept it: the replay
; decides the array equality by its lowering and the read from the
; certified contents, both relative to the surrogate's value, so under an
; active array equality it is not an exact evaluation of the original
; formula. Once answered sat here.
;
; RUN: %solver --array-equality --fp-abstraction=true -d %s | %OutputCheck %s
; RUN: %solver --array-equality --fp-abstraction=true --fp-abstraction-repair=false -d %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_ABVFP)
(declare-const a (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-const b (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-const x1 (_ FloatingPoint 8 24))
(declare-const x2 (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= a (store b #x1 (fp.mul RNE x1 y))))
(assert (fp.isNormal x1))
(assert (fp.isNormal y))
(assert (fp.eq x1 x2))
(assert (not (= (select a #x1) (fp.mul RNE y x2))))
(check-sat)
