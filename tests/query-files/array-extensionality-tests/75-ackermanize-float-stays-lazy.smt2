; RUN: %solver --array-equality --ackermanize %s 2>&1 | %OutputCheck %s
; CHECK-L: Warning: --ackermanize is disabled for queries with array equality over floating-point sorts.
; CHECK: ^unsat
; Float cells quotient their bit patterns (every NaN payload is one
; value), so the pointwise bit instantiation of the eager path would be
; stronger than value equality; such solves fall back to lemmas on
; demand, with a warning, and still decide correctly.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 2) (_ FloatingPoint 3 5)))
(declare-fun b () (Array (_ BitVec 2) (_ FloatingPoint 3 5)))
(declare-fun i () (_ BitVec 2))
(assert (= a b))
(assert (not (fp.eq (select a i) (select b i))))
(assert (not (fp.isNaN (select a i))))
(check-sat)
