; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The two zeros are different floating-point values under =, so equal
; arrays cannot hold +zero and -zero at the same index.
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(declare-fun b () (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
(assert (= a b))
(assert (= (select a #b0) (_ +zero 8 24)))
(assert (= (select b #b0) (_ -zero 8 24)))
(check-sat)
