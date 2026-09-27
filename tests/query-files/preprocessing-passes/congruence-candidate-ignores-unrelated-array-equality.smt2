; The two dividends are a pairing that is not a theorem, and neither
; mentions an array. The array equality is asserted on its own, yet the
; sub-solve used to be checked against its lowering all the same: leaving
; equality proxies out of the candidates is not enough.
; RUN: %solver -d --array-equality --congruence-candidates=1 %s | %OutputCheck %s
; RUN: %solver -d --array-equality --congruence-candidates=1 --array-ackermann-budget=0 %s | %OutputCheck %s
; CHECK: ^sat
(set-logic QF_ABV)
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(declare-const r (_ BitVec 8))
(declare-const x4 (Array (_ BitVec 10) (_ BitVec 4)))
(declare-fun a () (Array (_ BitVec 10) (_ BitVec 4)))
(assert (distinct x4 a))
(assert (bvult (bvudiv (bvadd p q) r) (bvudiv (bvmul p q) r)))
(check-sat)
(exit)
