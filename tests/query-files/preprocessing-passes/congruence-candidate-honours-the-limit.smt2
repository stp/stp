; How many candidates may be put to the solver. Each is its own query, so
; this is what the pass costs where nothing turns out to be equal; zero
; leaves the query exactly as it arrived.
; RUN: %solver -s --congruence-candidates=1 --congruence-candidate-limit=0 %s 2>&1 | %OutputCheck %s
; CHECK: tested:0 proved:0
; CHECK: ^unsat$
;
; The same query with candidates allowed.
; RUN: %solver -s --congruence-candidates=1 %s 2>&1 | %OutputCheck --check-prefix=ON %s
; ON: tested:[1-9]
; ON: ^unsat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert
  (not (=
    (bvudiv (bvadd (bvmul (_ bv3 16) a) (bvsub b a)) d)
    (bvudiv (bvadd (bvadd a a) (bvadd b (_ bv0 16))) d))))
(check-sat)
(exit)
