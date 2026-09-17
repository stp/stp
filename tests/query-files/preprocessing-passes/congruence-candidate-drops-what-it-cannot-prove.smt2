; A pairing the query offers that is not a theorem. Both dividends sit in
; the same slot of the same division, so the pass proposes them, but they
; differ wherever b does -- the sub-solve finds a model and the candidate is
; dropped.
;
; Nothing is asserted, and the query keeps the answer it had. A pass that
; assumed its candidates rather than proving them would answer unsat here.
; RUN: %solver -s --congruence-candidates=1 %s 2>&1 | %OutputCheck %s
; CHECK: tested:[1-9] proved:0
; CHECK: ^sat$
;
; RUN: %solver %s | %OutputCheck --check-prefix=OFF %s
; OFF: ^sat$
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert (not (= (bvudiv (bvadd a b) d) (bvudiv (bvsub a b) d))))
(check-sat)
(exit)
