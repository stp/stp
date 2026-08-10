; RUN: %solver --flattening=true --common-subsum=true -d %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The satisfiable companion, run with -d so the counterexample is built and
; checked against the original query: if the extraction alters an addition's
; value the recovered model will not satisfy the input.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (= (bvmul y (bvadd x x x x x y)) (_ bv100 8)))
(assert (= (bvmul z (bvadd x x x x x z)) (_ bv200 8)))
(assert (bvugt x (_ bv200 8)))
(check-sat)
