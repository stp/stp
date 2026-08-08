; RUN: %solver --flattening=true --common-subsum=true %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Common sub-sum extraction must handle an addition whose operands repeat.
; An operand appearing k times yields the same candidate pair C(k,2) times;
; counting those separately used to make the substitution run repeatedly on
; one addition, appending the shared node without a matching removal and so
; changing the addition's value. The multiplications keep the additions from
; being solved away word-level, so the extraction really runs here.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(assert (= (bvmul y (bvadd x x x x x y)) (_ bv0 8)))
(assert (= (bvmul z (bvadd x x x x x z)) (_ bv33 8)))
(assert (bvugt x (_ bv250 8)))
(check-sat)
