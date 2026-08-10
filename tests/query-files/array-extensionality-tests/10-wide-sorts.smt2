; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Independent index/element widths (Array BV32 BV8).
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun i () (_ BitVec 32))
(assert (= a b))
(assert (distinct (select a i) (select b i)))
(check-sat)
