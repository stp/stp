; RUN: %solver -d --congruence-candidates=1 %s | %OutputCheck %s
; RUN: %solver -d %s | %OutputCheck %s
; CHECK: ^sat
;
; The two bvurem applications share a divisor, so their dividends are a
; congruence pairing. The sub-solve that would prove them equal blasts them
; directly, and array reads that survive Ackermannisation have not been
; through the array transformer at that point: this used to hand a READ to
; the bit-blaster. Reduced from a fuzzer case.
(set-logic QF_ABV)
(declare-const v (_ BitVec 1))
(declare-const v12 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(declare-const x (Array (_ BitVec 14) (_ BitVec 9)))
(declare-fun a () (Array (_ BitVec 14) (_ BitVec 9)))
(assert (distinct (or (bvult (select x (_ bv1 14)) (select x ((_ zero_extend 6) ((_ zero_extend 7) v12)))) (not (bvusubo (_ bv0 9) (bvurem (select x ((_ zero_extend 5) (select x (_ bv0 14)))) (select a ((_ zero_extend 5) (select x ((_ sign_extend 7) ((_ zero_extend 6) v))))))))) (ite (= (_ bv0 9) (select x ((_ sign_extend 5) (select x ((_ zero_extend 6) ((_ zero_extend 7) v1)))))) false (bvugt (_ bv1 9) (bvurem (bvxor (select a (_ bv1 14)) (select a (_ bv0 14))) (select a ((_ zero_extend 5) (select x ((_ sign_extend 7) ((_ zero_extend 6) v))))))))))
(check-sat)
(exit)
