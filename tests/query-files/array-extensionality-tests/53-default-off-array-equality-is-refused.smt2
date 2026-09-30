; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^unsat$
; QF_ABV selects extensionality: equal arrays cannot disagree at an index.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(assert (= a b))
(assert (distinct (select a i) (select b i)))
(check-sat)
