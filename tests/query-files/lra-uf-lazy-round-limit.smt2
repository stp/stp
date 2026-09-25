; RUN: %solver --SMTLIB2 -s --uf-lazy-round-limit 1 %s 2>&1 | %OutputCheck %s
;
; The round limit. Each lazy round is a whole re-solve, so a declaration that
; keeps breaking congruence is paying that price for a few pairs at a time;
; past the limit, every pair it has left is stated at once. With the limit at
; one, the first round this declaration breaks in is the last: the next round
; carries its whole relation, and the answer is the one the pairs give.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (and (<= 0.0 a) (<= a 1.0)))
(assert (and (<= 0.0 b) (<= b 1.0)))
(assert (and (<= 0.0 c) (<= c 1.0)))
(assert (= (f a) 1.0))
(assert (= (f b) 2.0))
(assert (= (f c) 3.0))
; CHECK: rounds=2 lemmas=3 expanded=1
; CHECK: ^sat
(check-sat)
