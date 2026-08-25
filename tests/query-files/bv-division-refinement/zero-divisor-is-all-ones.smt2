; SMT-LIB totalises division by zero to all ones. Also already decided
; before the fact existed, and also here to stay that way.
; RUN: %solver --uninterpreted-functions --array-equality --uf-ackermann=auto --bv-term-abstraction=1 %s | %OutputCheck %s
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec 256))
(declare-fun b () (_ BitVec 256))
(assert (= b (_ bv0 256)))
(assert (distinct (bvudiv a b) (bvnot (_ bv0 256))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
